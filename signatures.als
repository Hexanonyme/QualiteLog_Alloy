open util/ordering[Commande] as co
open util/ordering[Time] as to
open util/integer as integer

sig Time {}

sig Position
{
	nord : lone Position,
	est : lone Position,
	sud : lone Position,
	ouest : lone Position,
	x : Int,
	y : Int
}

one sig TopLeft extends Position {}

one sig TopRight extends Position {}

one sig BottomLeft extends Position {}

one sig BottomRight extends Position {}

one sig Entrepot
{
	cmdALivrer: set Commande,
	currentCmd: cmdALivrer lone ->Time,
	pos: one Position
}

sig Receptacle
{	
	pos: one Position,
	rcap: Int[7] // valeur à revoir
}

sig Drone 
{
	positions: set Position,
	pos : positions one -> Time,
	cmd : Commande lone -> Time,
	dcap : Int[7], // valeur à revoir
	charge: Int one -> Time, 
	batterie : Int one -> Time 
}

sig Commande
{
	produit : some Produit,
	rec: one Receptacle
}

sig Produit {}


