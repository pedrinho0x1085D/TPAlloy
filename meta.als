
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
--a instanciação de um field é uma relação, ou seja um conjunto de tuplos, onde cada tuplo é uma 
--sequência de átomos. O mesmo átomo pode aparecer em duas posições diferentes no mesmo tuplo,
-- ou seja pode estar “relacionado” com átomos diferentes dependendo da sua posição em cada tuplo. 
--Penso que o caminho mais simples a seguir para representar os tuplos é usar algo parecido com o que
-- fez para os tipos dos fields.
sig Atom {
	name : one Name
}

sig Instance {
	atoms : set Atom
}

pred solve [m : Model, i : Instance] {
	valid[m]
	i.atoms.name in m.sigs.name
	Abstract.name not in i.atoms.name	
}

run solve for 3 but 1 Model, 1 Instance


