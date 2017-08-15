module Sales

enum 項目種別{数量, FTE}

sig 受注{
	内容: some 小項目
}
sig 小項目{
	種別: 項目種別
}{
	-- 小項目の親はひとつ
	one 内容.this
}

abstract sig time{}
sig 売上計画{
	対象受注: 受注,
	〆: time
}

abstract sig 予定{
	時期: 売上計画,
	項目: 小項目
}{
	-- 売上計画の対象受注と売上予定の小項目の属する受注とは合致する
	時期.@対象受注 = 項目.~@内容
}

assert 売上予定項目は売上計画の受注に含まれる{
	all x: 予定 | x.項目 in x.時期.対象受注.内容
}
check 売上予定項目は売上計画の受注に含まれる

sig 数量予定 extends 予定{
}{
	-- 受注内容の小項目と整合する
	項目.種別 = 数量
	-- 同一時期に同一項目への予定はただひとつ
	no x: 時期.~@時期 - this | x.@項目 = 項目
}

assert 同時期にひとつの項目に対して複数の数量予定はない{
	no disj x, x': 数量予定 | x.時期 = x'.時期 and x.項目 = x'.項目
}
check 同時期にひとつの項目に対して複数の数量予定はない for 6 but exactly 3 数量予定

sig 担当{}
sig FTE予定 extends 予定{
	アサイン: 担当
}{
	-- 受注内容の小項目と整合する
	項目.種別 = FTE
	-- 同一時期に同一項目への予定は担当者につきただひとつ
	no x: 時期.~@時期 - this | x.@項目 = 項目 and x.@アサイン = アサイン
}
assert 同時期にひとつの項目に対するひとりの担当者による複数のFTE予定はない{
	no disj x, x': FTE予定 | x.時期 = x'.時期 and x.項目 = x'.項目 and x.アサイン = x'.アサイン
}
check 同時期にひとつの項目に対するひとりの担当者による複数のFTE予定はない for 6 but exactly 3 FTE予定

pred show{
--	some FTE予定
--	some 数量予定
--	#受注 > 1
--	some disj x, x': FTE予定 | x.項目 != x'.項目 and x.時期 = x'.時期
}
run show
