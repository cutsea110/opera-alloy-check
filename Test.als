module Test

open util/ordering[Time]

sig Time{}

abstract sig 乗組員{}
one sig 農夫 extends 乗組員{}
one sig キャベツ extends 乗組員{}
one sig 山羊 extends 乗組員{}
one sig 狼 extends 乗組員{}

abstract sig 場所{
	居る: 乗組員 -> Time
}
one sig 向岸 extends 場所{}
one sig 此岸 extends 場所{}
one sig 舟 extends 場所{
	着: (向岸 + 此岸) one -> Time
}

fact 常に一箇所に存在する{
	all t: Time, x: 乗組員 | one 居る.t.x
}

fact ヤギとキャベツ{
	all t: Time | no p: 場所 | (山羊 + キャベツ) in p.居る.t and 農夫 not in p.居る.t
}
fact ヤギと狼{
	all t: Time | no p: 場所 | (山羊 + 狼) in p.居る.t and 農夫 not in p.居る.t
}
fact 定員{
	all t: Time - first | #舟.居る.t <= 2 and 農夫 in 舟.居る.t
}

pred init(t: Time){
	(農夫 + 山羊 + キャベツ + 狼) in 此岸.居る.t
	舟.着.t in 此岸
}
pred done(t: Time){
	(農夫 + 山羊 + キャベツ + 狼) in (舟 + 向岸).居る.t
}

fun 対岸(p: 場所 - 舟) : one 場所 - 舟 {
	(場所 - 舟) - p
}

fact Traces{
	first.init
	all t: Time - last | let t' = t.next {
		-- 舟は岸を往復
		舟.着.t' = 対岸[舟.着.t]
		let 此岸メンバ = 此岸.居る.t, 向岸メンバ = 向岸.居る.t, 舟上メンバ = 舟.居る.t {
			舟.着.t in 此岸 => let 入れ替えメンバ = 此岸メンバ + 舟上メンバ {
				舟.居る.t' in 入れ替えメンバ and 此岸.居る.t' in 入れ替えメンバ and 向岸.居る.t' = 向岸.居る.t
				}
			舟.着.t in 向岸 => let 入れ替えメンバ = 向岸メンバ + 舟上メンバ {
				舟.居る.t' in 入れ替えメンバ and 向岸.居る.t' in 入れ替えメンバ and 此岸.居る.t' = 此岸.居る.t
				}
			}
		}
	last.done
}

pred show {}
run show for 8 Time
