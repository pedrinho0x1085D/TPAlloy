
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

/**

1)Assegurar que os nomes são únicos
2)Assegurar que os nomes existem no conjunto de nomes de Signature
3)Assegurar que os nomes de campos de assinaturas são únicos
4) Assegurar que os tipos são acíclicos.
*/

pred valid[m : Model] {
	all n : Name | lone name.n & m.sigs
	all n: Field.types.name| n in Signature.name
	all f:Signature.fields | f not in Signature.fields-f
	all t:Type | t not in t.~next
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


