open util/ordering[Commande] as co
open util/ordering[Time] as to
open util/integer as integer

//Signatures :

sig Time {}

sig Position
{
	nord : lone Position,
	est : lone Position,
	sud : lone Position,
	ouest : lone Position,
	x : Int,
	y : Int,
	isReceptacle : Int
}

one sig TopLeft extends Position {}

one sig TopRight extends Position {}

one sig BottomLeft extends Position 
{
}

one sig BottomRight extends Position {}

one sig Entrepot extends Receptacle
{

	cmdALivrer: set Commande,
	currentCmd: cmdALivrer one ->Time 
}

sig Drone 
{
	positions: set Position,
	pos : positions one -> Time,
	cmd : Commande lone -> Time,
	dcap : Int[5], // valeur à revoir
	charge: Int one -> Time, 
	batterie : Int one -> Time 
}

sig Produit
{
}

sig Commande
{
	produit : some Produit,
	rec: one Receptacle
}

fact 
{
    #((Commande -> Entrepot) & rec)=0
}

sig Receptacle
{	
	pos: one Position,
	charge : Int one -> Time,
	rcap: Int[5] // valeur à revoir
}
