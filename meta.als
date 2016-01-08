
sig Model {
	sigs : set Signature
}

sig Field{
	name: one Name,
	types: one Type,
	mult: one Mult
}
/**
	Multiplicidades.
*/ 
abstract sig Mult{}
one sig Lone extends Mult {}
one sig One extends Mult {}
one sig Some extends Mult {}
one sig Set extends Mult {}

sig Type{
	name: one Name,
	next: lone Type
}
/**
Adições:
	1) Campo, com tipo.
	2) Extensão de assinaturas
*/
sig Signature {
	name : one Name,
	fields: some Field,
	extend: lone Signature
}
/**
Sig Abstrata. 
*/
sig Abstract extends Signature{}
/**

1)Assegurar que os nomes são únicos
2)Assegurar que os nomes existem no conjunto de nomes de Signature
3)Assegurar que os nomes de campos de assinaturas são únicos
4) Assegurar que os tipos são acíclicos.
*/

pred valid[m : Model] {
	all n : Name | lone name.n & m.sigs
	all n: Field.types.name| n in Signature.name
	all f:Field | lone fields.f.name & m.sigs.fields.name
	all t:Type | t not in t.^next
	all t1:Type, t2:Type | t1!=t2 implies t1.name!=t2.name
	all s:Signature | s not in s.^extend
}

run valid for 3 but 1 Model, 0 Instance

run {some m : Model | not valid[m]} for 3 but 1 Model, 0 Instance

sig Name {}
sig Atom {
	name : one Name,

}
sig Relation{
	tuplos: set Tuple
}

sig Tuple{
	seqAtom : one SeqAtom
}

sig SeqAtom{
	atom: one Atom,
	next: lone SeqAtom
}

sig Instance {
	atoms : set Atom,
	relations : some Relation
}

pred solve [m : Model, i : Instance] {
-- Apenas faz solve se o modelo for valid
	valid[m]
-- Povoar nomes das signatures, Abstract não entra!
	i.atoms.name in m.sigs.name-Abstract.name
-- Povoar as relations
	i.relations.tuplos.seqAtom.atom in i.atoms
	all relat:i.relations,fie:m.sigs.fields | compat[relat.tuplos.seqAtom,fie.types]
}

pred compat[seqA:SeqAtom,type:Type]{
	#(seqA.atom + seqA.^next)=#(type+ type.^next)
	all at:(seqA.atom + seqA.^next), ty:(type + type.^next) |#(at.~(^next)) = #(ty.~(^next))
	
}


run solve for 3 but 1 Model, 1 Instance


