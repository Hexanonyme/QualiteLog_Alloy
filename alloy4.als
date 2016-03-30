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
	y : Int
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
	pos: one Position
}

/* Capacités de produits */
one sig Capacite
{
	dcap : Int[5], // !!! valeurs à revoir
	rcap: Int[5]
}

sig Drone 
{
	positions: set Position,
	pos : positions one -> Time,
	cmd : lone Commande,
	charge: Int one -> Time, // nb de produits
	batterie : Int one -> Time // !!! à revoir si initialisation ici
}

sig Produit
{
}

sig Commande
{
	produit : some Produit,
	rec: one Receptacle
}


sig Receptacle
{	
	pos: one Position,
	charge : Int one -> Time
}
