-- | SMOMO以来の標準的な承認フロー
-- 承認は複数人による多段階の承認を要求するが,
-- 最終承認では別のインスタンスへの影響を持ち,そのために不可逆つまり巻き戻しはできない.
-- 外部連携や,プロジェクトの状態を変えるなど,それによって他の処理も連鎖的に動作が影響を受けるために
-- 巻き戻しはシステムでは禁止されている.
-- 最終承認以外の承認ステップはそうした効果を持たないためいつでも差し戻しや却下によりドラフト状態や破棄することさえ可能になる.
--
-- OPERAでは前受金請求や立替請求，前受取崩など新規に起こすところから承認するものはこのフローになる.
-- 【対象外】
--  1. 委託料の請求書(これは承認しか最終状態を認めない.破棄されるとマズい)
--  2. 業務終了報告書確認書(これは外部へのインパクトを持つ承認が2回起こる)
module Approve

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
enum Status { New               -- メモリ上で生成(DBにはない)
                   , Draft             -- DBに保存
                   , Requested       -- 申請中(=承認待ち)
                   , Confirmed       -- 確認(最終承認ではないものをシステムでは通常承認と呼ぶ)
                   , Approved        -- 承認済
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
		r.status.t in (Approved + Vanished + InTrash)
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

assert 一旦破棄されたら他の状態になるものはない{
	all r: Report | some t: Time - last | r.status.t in InTrash
	 => { no t': t.^next | r.status.t' in (Status - InTrash) }
}
check 一旦破棄されたら他の状態になるものはない for 3 but exactly 3 Report, 15 Time

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
