/* Capacités */

//open util/ordering[Commande] as co
open util/ordering[Time] as to
open util/integer as integer

//Signatures :
sig Time {}

sig Position
{
	nord : one Position,
	est : one Position,
	sud : one Position,
	ouest : one Position
}

one sig Capacite
{
	dcap : Int[3],
	rcap: Int[3]
}

sig Drone 
{
	pos: one Position,
	//cmd : lone Commande,
	charge: Int[0],
	batterie : Int[3] //à revoir si initialisation ici
}

/*sig Produit
{
}

sig Commande
{
	produit : some Produit,
	rec: one Receptacle
}

one sig Entrepot
{
	cmdALivrer: set Commande,
	pos: one Position
}

sig Receptacle
{	
	pos: one Position
}*/

fun inc [n : Int]: Int 
{
 add [n,Int[1]] 
}

//Prédicats :

pred chargerBatterie [ d: Drone]
{
	// batterie ++
}

pred livrerProduits [ d: Drone]
{
	// charge à 0
}

//Faits :

fact energie
{
	all d : Drone | d.batterie >= Int[0] && d.batterie <= Int[3]
}

fact charge
{
	all d : Drone, c : Capacite | d.charge <= c.dcap
}

/* Un drone ne peut pas livrer ses produits et recharger sa batterie en même temps */
fact NoLivraisonBatterie
{
	all d : Drone | livrerProduits[d]  != chargerBatterie[d]
}

//Assertions :

/*assert DroneEntrepot 
{		
	all d : Drone, t: Time | let t' = t.next
	{
		augmenteBatterie[d, t, t']
	}
}*/

pred go{}
run go{}

//check DroneEntrepot for 1

