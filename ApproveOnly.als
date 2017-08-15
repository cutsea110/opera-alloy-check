-- | OPERAの委託料請求書の承認
-- Approval.alsとの差としては承認しか最終状態を許容しない.
-- なぜなら委託料請求書が存在している前提として売上が発生しており,SAP連携による外部システムへの不可逆な効果が発生してしまっているから.
module ApproveOnly

open util/ordering[Time]
open util/boolean

sig Time{}

-- Repertと言っているがBillです.
sig Report{
	status: Status one -> Time,
	is_hold: Bool one -> Time,
	ev: Event one -> Time
}

------------------------------------------------------------------
-- 状態
------------------------------------------------------------------
enum Status { Draft             -- DBに保存
                   , Requested       -- 申請中(=承認待ち)
                   , Confirmed       -- 確認(最終承認ではないものをシステムでは通常承認と呼ぶ)
                   , Approved        -- 承認済
                   }

------------------------------------------------------------------
-- イベント
------------------------------------------------------------------
enum Event { 生成
                  , 保存
                  , 申請
                  , 確認
                  , 承認
                  , 申請者差し戻し
                  , 確認者差し戻し
                  , 却下
                  , 保留
                  , 保留解除
                  }


------------------------------------------------------------------
-- 承認アクション
--
-- 誰がアクションを起こせるかはここでは捨象する.
-- イベント化してないので差し戻しなのか却下なのか区別できない.
------------------------------------------------------------------

-- | 保存処理
-- 【事前条件】 status: Draft           is_hold: b
-- 【事後条件】 status: Draft           is_hold: b(不変)
pred 保存(t,t':Time, r: Report){
	r.status.t in Draft and

	r.status.t' in Draft and
	r.is_hold.t' = r.is_hold.t and

	r.ev.t' in 保存
}

-- | 申請処理
-- 【事前条件】 status: Draft           is_hold: b
-- 【事後条件】 status: Requested       is_hold: False
pred 申請(t,t': Time, r: Report){
  r.status.t in Draft and

	r.status.t' in Requested and
	r.is_hold.t' = False and

	r.ev.t' in 申請
}

-- | 確認処理(最終承認以外の承認)
-- 【事前条件】 status: Requested       is_hold: b
-- 【事後条件】 status: Confirmed       is_hold: False
pred 確認(t,t': Time, r: Report){
  r.status.t in Requested and

	r.status.t' in Confirmed and
	r.is_hold.t' = False and

	r.ev.t' in 確認
}

-- | 承認処理
-- 【事前条件】 status: Confirmed       is_hold: b
-- 【事後条件】 status: Approveed       is_hold: False
pred 承認(t,t': Time, r: Report){
  r.status.t in Confirmed and

	r.status.t' in Approved and
	r.is_hold.t' = False and

	r.ev.t' in 承認
}

-- | 申請者差し戻し処理
-- 【事前条件】 status: Requested か Confirmed      is_hold: b
-- 【事後条件】 status: Draft                       is_hold: False
pred 申請者差し戻し(t,t': Time, r: Report){
  r.status.t in (Requested + Confirmed) and

	r.status.t' in Draft and
	r.is_hold.t' = False and

	r.ev.t' in 申請者差し戻し
}

-- | 確認者差し戻し処理
-- 【事前条件】 status: Confirmed       is_hold: b
-- 【事後条件】 status: Requested       is_hold: False
pred 確認者差し戻し(t,t': Time, r: Report){
  r.status.t in Confirmed and

	r.status.t' in Requested and
	r.is_hold.t' = False and

	r.ev.t' in 確認者差し戻し
}

-- TODO: 却下はどこまで戻すか制御できても良いがまずは完全に元に戻すとしよう
-- | 却下処理
-- 【事前条件】 status: Requested か Confirmed      is_hold: b
-- 【事後条件】 status: Draft                       is_hold: False
pred 却下(t,t': Time, r: Report){
	r.status.t in (Requested + Confirmed) and

	r.status.t' in Draft and
	r.is_hold.t' = False and

	r.ev.t' in 却下
}


-- | 保留
-- 【事前条件】 status: s(Approved除く) is_hold: False
-- 【事後条件】 status: s(不変)         is_hold: True
pred 保留(t,t': Time, r: Report){
  r.status.t not in Approved and 
	r.is_hold.t = False and

	r.status.t' = r.status.t and
	r.is_hold.t' = True and

	r.ev.t' in 保留
}

-- | 保留解除
-- 【事前条件】 status: s               is_hold: True
-- 【事後条件】 status: s(不変)         is_hold: False
pred 保留解除(t,t': Time, r: Report){
	r.is_hold.t = True and

  r.status.t' = r.status.t and
	r.is_hold.t' = False and

	r.ev.t' in 保留解除
}

-- | 現状維持(これはAlloy上での単なる時間経過なので実装上のアクションではない)
-- 【事前条件】 status: s               is_hold: b
-- 【事後条件】 status: s(不変)         is_hold: b(不変)
pred 現状維持(t,t': Time, r: Report){
  r.status.t' = r.status.t and
	r.is_hold.t' = r.is_hold.t and

	r.ev.t' = r.ev.t
}

------------------------------------------------------------------
-- 関数
------------------------------------------------------------------
------------------------------------------------------------------
-- トレース
------------------------------------------------------------------
pred init(t: Time){
  all r: Report{
		r.status.t in Draft and
		r.is_hold.t = False and
		r.ev.t in 生成
	}
}

fact Traces{
	first.init
	all t: Time - last | let t' = t.next {
		all r: Report {
			保存[t, t', r] or
			申請[t, t', r] or
			確認[t, t', r] or
			承認[t, t', r] or
			申請者差し戻し[t, t', r] or
			確認者差し戻し[t, t', r] or
			却下[t, t', r] or
			保留[t, t', r] or
			保留解除[t, t', r] or
			現状維持[t, t', r]
		}
	}
}

-- どの請求書もいつかは終了状態(承認済)に到達しうるという時相論理を提供したいが
-- lastにしちゃうとそこから別状態にいかないことの検証ができないのでこうした.
fact canFinished{
  all r: Report | some t: Time {
		r.status.t in Approved
	}
}

------------------------------------------------------------------
-- 検査
------------------------------------------------------------------
assert 一旦承認されたら他の状態になることはない{
	all r: Report | some t: Time - last | r.status.t in Approved
	 => { no t': t.^next | r.status.t' in (Status - Approved) }
}
check 一旦承認されたら他の状態になることはない for 3 but exactly 3 Report, 15 Time

assert 承認状態で保留はありえない{
	all r: Report | no t: Time | r.status.t in Approved and r.is_hold.t = True
}
check 承認状態で保留はありえない for 3 but exactly 3 Report, 15 Time

------------------------------------------------------------------
-- 効率のため
------------------------------------------------------------------

pred 承認されるものがある{
	some r: Report| some t: Time{
		r.status.t in Approved
	}
}

------------------------------------------------------------------
-- 実行
------------------------------------------------------------------
pred show{
  承認されるものがある[]
}
-- アクションが11しかないので15tickあればスコープ十分なはず?
run show for 3 but exactly 3 Report, 15 Time
