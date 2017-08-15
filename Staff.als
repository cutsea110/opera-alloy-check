module Staff

-- シミックグループ会社
sig 会社{}

-- システム利用者
sig ユーザ{
	所属: some 会社,
	役割: 所属 -> some ロール
}

abstract sig ロール{}
one sig 実施部門 extends ロール{}
one sig 業務管理部 extends ロール{}
one sig 経理 extends ロール{}
one sig BD extends ロール{}

pred show{
}
run show
