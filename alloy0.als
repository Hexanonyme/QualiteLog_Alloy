open util/ordering[Commande] as co
open util/ordering[Time] as to

//Signatures :
sig Time {}

sig Position
{
	nord : one Position,
	est : one Position,
	sud : one Position,
	ouest : one Position
}

sig Capacite
{
}

sig Drone 
{
	//capacite : one int,
	pos: one Position,
	//cmd : lone Commande
}

sig Produit
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
}

//Prédicats :
pred init [t: Time] 
{

}

pred deplacerDrones [t, t' : Time, d : Drone] 
{
	
}


//Faits :
fact traces 
{
    init [first]	
	//Boucle
    all t: Time-last | let t' = t.next
    {
       all d : Drone | deplacerDrones [t, t', d]
    }
}

//Assertions :
assert PlsDroneMemeEndroit
{
	all t: Time, d : Drone |
		let t' = t.next
		{
			deplacerDrones [t, t', d] and all d2 : Drone
			{
				d.pos = d2.pos
			}
		}
}

check PlsDroneMemeEndroit for 2
