-- | 業務終了報告書確認書の承認(不可逆な処理)が2段階あるケース
-- 業務終了報告書確認書の承認フローは
--  1. SAP連携して実際に売上が上がるトリガーとしての承認
--  2. 請求して良いと判断され請求書が生成されるトリガーとしての業務終了内容確認という名の承認
-- の2段階がある.
-- 厳密には2の方はOPERA内部でまだ閉じているため全く取り返しがつかないというわけではないが
-- ひとまず不可逆な処理であるという前提で検証する.
module Approve2Step

open util/ordering[Time]
open util/boolean

sig Time{}

sig Report{
	status: Status one -> Time,
	is_hold: Bool one -> Time,
	ev: Event one -> Time
}

------------------------------------------------------------------
-- 状態
------------------------------------------------------------------
enum Status { New               -- メモリ上に生成
                   , Draft             -- DBに保存
                   , Requested       -- 申請中(=承認待ち)
                   , Confirmed       -- 確認(最終承認ではないものをシステムでは通常承認と呼ぶ)
                   , Approved        -- 承認済
                   , Published       -- 発行済
                   , InTrash           -- 破棄状態(論理削除相当)
                   , Vanished         -- メモリ上で破棄
                   }

------------------------------------------------------------------
-- イベント
------------------------------------------------------------------
enum Event { 生成
                  , 保存
                  , 申請
                  , 確認
                  , 承認
                  , 発行
                  , 破棄
                  , 申請者差し戻し
                  , 確認者差し戻し
                  , 却下
                  , 保留
                  , 保留解除
                  , 消滅
                  }

------------------------------------------------------------------
-- 承認アクション
--
-- 誰がアクションを起こせるかはここでは捨象する.
-- イベント化してないので差し戻しなのか却下なのか区別できない.
------------------------------------------------------------------

-- | 保存しない
-- 【事前条件】 status: New             is_hold: b
-- 【事後条件】 status: Vanished        is_hold: b(不変)
pred 保存しない(t,t':Time, r: Report){
	r.status.t in New and

	r.status.t' in Vanished and
	r.is_hold.t' = r.is_hold.t and

	r.ev.t' in 消滅
}

-- | 保存処理
-- 【事前条件】 status: New か Draft    is_hold: b
-- 【事後条件】 status: Draft           is_hold: b(不変)
pred 保存(t,t':Time, r: Report){
	r.status.t in (New + Draft) and

	r.status.t' in Draft and
	r.is_hold.t' = r.is_hold.t and

	r.ev.t' in 保存
}

-- | 申請処理
-- 【事前条件】 status: New か Draft    is_hold: b
-- 【事後条件】 status: Requested       is_hold: False
pred 申請(t,t': Time, r: Report){
  r.status.t in (New + Draft) and

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

-- | 発行処理
-- 【事前条件】 status: Approved        is_hold: b
-- 【事後条件】 status: Published       is_hold: False
pred 発行(t,t': Time, r: Report){
  r.status.t in Approved and

	r.status.t' in Published and
	r.is_hold.t' = False and

	r.ev.t' in 発行
}

-- | 破棄
-- 【事前条件】 status: Draft           is_hold: b
-- 【事後条件】 status: InTrash         is_hold: b(不変)
pred 破棄(t,t': Time, r: Report){
  r.status.t in Draft and

	r.status.t' in InTrash and
	r.is_hold.t' = r.is_hold.t and

	r.ev.t' in 破棄
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
-- 【事前条件】 status: s(Published除く) is_hold: False
-- 【事後条件】 status: s(不変)         is_hold: True
pred 保留(t,t': Time, r: Report){
  r.status.t not in Published and 
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
		r.status.t in New and
		r.is_hold.t = False and
		r.ev.t in 生成
	}
}

fact Traces{
	first.init
	all t: Time - last | let t' = t.next {
		all r: Report {
			保存しない[t, t', r] or
			保存[t, t', r] or
			申請[t, t', r] or
			確認[t, t', r] or
			承認[t, t', r] or
			発行[t, t', r] or
			破棄[t, t', r] or
			申請者差し戻し[t, t', r] or
			確認者差し戻し[t, t', r] or
			却下[t, t', r] or
			保留[t, t', r] or
			保留解除[t, t', r] or
			現状維持[t, t', r]
		}
	}
}

-- どの報告書もいつかは終了状態に到達しうるという時相論理を提供したいが
-- lastにしちゃうとそこから別状態にいかないことの検証ができないのでこうした.
fact canFinished{
  all r: Report | some t: Time {
		r.status.t in (Published + Vanished + InTrash)
	}
}

------------------------------------------------------------------
-- 検査
------------------------------------------------------------------
assert 一旦発行されたら他の状態になることはない{
	all r: Report | some t: Time - last | r.status.t in Published
	 => { no t': t.^next | r.status.t' in (Status - Published) }
}
check 一旦発行されたら他の状態になることはない for 3 but exactly 3 Report, 15 Time

assert 承認済になったら破棄や削除はされない{
	all r: Report | some t: Time - last | r.status.t in Approved
	 => { no t': t.^next | r.status.t' in (InTrash+Vanished) }
}
check 承認済になったら破棄や削除はされない for 3 but exactly 3 Report, 15 Time

assert 承認済みになったらその後いつか必ず発行される{
	all r: Report | some t: Time - last | r.status.t in Approved
	 => { some t': t.^next | r.status.t' in Published }
}
check 承認済みになったらその後いつか必ず発行される for 3 but exactly 3 Report, 15 Time

assert 発行されたのであれば承認されている{
	all r: Report | some t: Time - last | r.status.t in Published
	 => { some t': t.^(~next) | r.status.t' in Approved }
}
check 発行されたのであれば承認されている for 3 but exactly 3 Report, 15 Time

assert 発行状態で保留はありえない{
	all r: Report | no t: Time | r.status.t in Published and r.is_hold.t = True
}
check 発行状態で保留はありえない for 3 but exactly 3 Report, 15 Time

assert 一旦破棄されたら他の状態になるものはない{
	all r: Report | some t: Time - last | r.status.t in InTrash
	 => { no t': t.^next | r.status.t' in (Status - InTrash) }
}
check 一旦破棄されたら他の状態になるものはない for 3 but exactly 3 Report, 15 Time

------------------------------------------------------------------
-- 効率のため
------------------------------------------------------------------

pred 発行されるものがある{
	some r: Report| some t: Time{
		r.status.t in Published
	}
}

------------------------------------------------------------------
-- 実行
------------------------------------------------------------------
pred show{
  発行されるものがある[]
}
-- アクションが11しかないので15tickあればスコープ十分なはず?
run show for 3 but exactly 3 Report, 15 Time
