
sig Model {
	sigs : set Signature
}

sig Field{
	name:one Name,
	next: lone Field
}
sig Signature {
	name : one Name,
	fields: some Field
}

pred valid[m : Model] {
	all n : Name | lone name.n & m.sigs
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


