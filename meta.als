sig Model{
	sigs : set Signature
}

sig Signature{
	name: one Name,
	fields: some Field
}

sig Field{
	name:one Name,
	next: lone Field
}

sig Name{}

sig Atom {
	name: one Name
}

sig Instance{
	atoms: set Atom
}

run valid for 3 but 1 Model, 1 Instance

pred valid[m:Model]{
	all n:Name | lone name.n & m.sigs
	--no 
}

pred solve [m:Model, i:Instance]{
	i.atoms.name in m.sigs.name
}
