
sig Model {
	sigs : set Signature
}

sig Field{
	name: one Name,
	types: one Type
}

sig Type{
	name: one Name,
	next: lone Type
}

sig Signature {
	name : one Name,
	fields: some Field
}
-- Atenção que também é necessário assegurar que os tipos são acíclicos.

pred valid[m : Model] {
	all n : Name | lone name.n & m.sigs
	all n: Type.name| n in Signature.name
	no t1:Type,t2:t1.next | t1.name=t2.name
}

run valid for 3 but 1 Model, 0 Instance

run {some m : Model | not valid[m]} for 3 but 1 Model, 0 Instance

sig Name {}

sig Atom {
	name : one Name
}

sig Instance {
	atoms : set Atom
}

pred solve [m : Model, i : Instance] {
	i.atoms.name in m.sigs.name
}

run solve for 3 but 1 Model, 1 Instance


