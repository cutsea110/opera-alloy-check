/*
 * CRAGEの見積の構造
 */
module CRAGE

sig 大項目{
	内容: some 中項目
}
sig 中項目{
	内容: some (グループ項目+小項目)
}{
  -- 小項目は必須
	some (内容 & 小項目)
}
sig グループ項目{
}
sig 小項目{
}

fact {
	all x: 中項目 | one 内容.x
	all x: 小項目 | one 内容.x
	all x: グループ項目 | one 内容.x
}

assert グループだけからなる中項目はない{
  all x:中項目 | let y = x.内容 | #(y - グループ項目) > 0
}
check グループだけからなる中項目はない

pred show {
}
run show
