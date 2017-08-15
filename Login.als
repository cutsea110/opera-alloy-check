module Login

open util/ordering[Time]

sig Time{}

sig 利用者{
}

sig パスワード{}

sig セッション{
	アカウント: one 利用者,
	所属: 会社 lone -> Time,
	役割: ロール -> Time,

	ログ: Event -> Time
}{
	-- 所属が入っていれば役割が入ってて, 
	-- システムが保持する利用者の認可情報と整合する.
	all t: Time | let cs = システム.認可[アカウント].ロール {
		some 所属.t => {
			所属.t in cs and システム.認可[アカウント][所属.t] = 役割.t
			} else no 役割.t
		}
	-- 所属が埋まるのは会社選択イベントのみ
	-- 所属は一度設定されたら不変
	all t: Time - last | let t' = t.next {
		no 所属.t and some 所属.t' <=> some e:会社選択 { e.pre = t and e.post = t' and e.session = this }
		some 所属.t => 所属.t' = 所属.t
		}
	-- ログに記録されるのはこのセッションで発生したイベントのみ
	ログ.Time.session in this
	all t: Time - last | let t' = t.next | some e: Event {
		e.pre = t and e.session = this => ログ.t' = ログ.t + e else ログ.t' = ログ.t
		}
}

sig 会社{}

abstract sig ロール{}
one sig BD extends ロール{}
one sig 実施部門 extends ロール{}
one sig 業務管理部 extends ロール{}
one sig 経理 extends ロール{}

one sig システム{
	認証: 利用者 -> one パスワード,
	認可: 利用者 -> some (会社 -> some ロール),
	接続: セッション -> Time
}{
	all t: Time | let t' = t.next {
		all s: (接続.t' - 接続.t) | some e:サインイン | e.pre = t and e.post = t' and e.session = s
		all s: (接続.t - 接続.t') | some e:サインアウト | e.pre = t and e.post = t' and e.session = s
		all s: (接続.t & 接続.t') | no e: (サインイン + サインアウト) { e.pre = t and e.post = t' and e.session = s}
		}
}

abstract sig Event{
	pre, post: Time,
	user: 利用者,
	session: セッション
}{
	-- セッションと利用者は整合
	session.アカウント = user
	-- これが必要そうなのが何故かは不明だが,いずれにせよ複数のイベントが重複することはない
	post = pre.next
	-- イベントログを残す
	session.ログ.post = session.ログ.pre + this
}

sig サインイン extends Event{
}{
	session not in システム.接続.(pre) and session in システム.接続.(post)
	no session.所属.(pre) and no session.所属.(post)
}

abstract sig RegularEvent extends Event{
}{
	session in システム.接続.(pre) and session in システム.接続.(post)
}

sig 会社選択 extends RegularEvent{
	指定: one 会社
}{
	no session.所属.(pre) and some session.所属.(post)
	指定 = session.所属.(post)
}

sig データ操作 extends RegularEvent{
	スコープ: some 会社
}{
	some session.所属.(pre) and session.所属.(pre) = session.所属.(post)
	スコープ = session.所属.(pre + post)
}

sig サインアウト extends Event{
}{
	session in システム.接続.(pre) and session not in システム.接続.(post)
	some session.所属.(pre) and session.所属.(pre) = session.所属.(post)
}

-- 検証
assert 選択した会社以外のデータを操作できない{
	all s:セッション {
		s.ログ.Time.スコープ in s.ログ.Time.指定
		}
}
check 選択した会社以外のデータを操作できない for 3 but 10 Event, 7 Time

-- これは反例(つまり操作できる)ので良い
assert 同時に違う会社のデータを操作することはない{
	no t: Time | some disj s, s': システム.接続.t | some disj e, e': データ操作{
			let c = s.所属.t, c' = s'.所属.t{
				-- 同時にデータ操作がある
				e.session = s and e'.session = s' and e.pre = t and e'.pre = t
				-- 同じ利用者が異なる会社でサインイン中
				s.アカウント = s'.アカウント and c != c'
				}
		}
}
check 同時に違う会社のデータを操作することはない for 3 but 10 Event, 7 Time


-- 探索効率のため
pred 同時に複数のイベントは起きない{
	all s: セッション {
		#s.~session = #s.~session.pre
		#s.~session = #s.~session.post
		}
}

pred イベントが一通り存在する{
	some サインイン
	some 会社選択
	some データ操作
	some サインアウト
}

pred いつも何かのイベントがある{
	all t: Time - last |	some e: Event { e.pre = t }
}

-- トレース
pred init(t: Time){
	no システム.接続.t
	all s: セッション | no s.ログ.t
}

fact Trace{
	first.init
}

pred show{
	同時に複数のイベントは起きない[]
	イベントが一通り存在する[]
--	いつも何かのイベントがある[]
}
run show for 3 but 10 Event, 7 Time
