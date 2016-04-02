open signatures

//Prédicats :

pred surEntrepot [ d:Drone, t:Time] 
{
	d.pos.t = Entrepot.pos 
}

pred surReceptacle [ d:Drone , t:Time]
{
	some r:Receptacle | (d.pos.t = r.pos) && !surBonReceptacle[d,t]
}

pred surBonReceptacle [ d:Drone , t:Time]
{
	d.pos.t = d.cmd.t.rec.pos 
}

pred positionConstante [ d:Drone, t:Time]
{
	let t' =t.next
	{
		d.pos.t' = d.pos.t
	}
}

 /* La capacité de la batterie d'un drone est de 3 unités d'énergie */	
pred batteriePleine [d:Drone, t:Time]
{
	eq[d.batterie.t, Int[3]]
}

pred batterieVide [d:Drone, t:Time]
{
	eq[d.batterie.t, Int[0]]
}

pred batterieConstante [ d: Drone, t:Time]
{
	let t' =t.next
	{
		d.batterie.t' = d.batterie.t
	}
}

pred chargeVide [ d:Drone, t:Time]
{	
	eq[d.charge.t, Int[0]]
}

pred chargeConstante [ d: Drone, t:Time]
{
	let t' =t.next
	{
		d.charge.t' = d.charge.t
	}
}

pred commandeDroneConstante [d:Drone, t:Time]
{
	let t'=t.next
	{
		d.cmd.t = d.cmd.t'
	}
}

pred commandeEntrepotConstante [d:Drone, t:Time]
{
	let t'=t.next
	{
		Entrepot.currentCmd.t = Entrepot.currentCmd.t'
	}
}

/* Un drone a une capacité DCAP */
pred chargeDroneMaximum [d:Drone, t:Time]
{
	d.charge.t = d.dcap
}

/* Un réceptacle est un conteneur de capacité RCAP */
pred chargeReceptacleMaximum [r:Receptacle, t:Time]
{
	r.charge.t = r.rcap
}

/* Un drone prend 1 unité de temps pour recharger sa batterie de 1 unité d'énergie */
pred chargerBatterie [ d: Drone, t:Time]
{
	let t' =t.next
	{
		!batteriePleine[d,t] => (d.batterie.t' = add[d.batterie.t, Int[1]]) else batterieConstante[d,t]
	}
	/*chargeConstante[d,t] and */commandeDroneConstante[d,t] and positionConstante[d,t]
}

/* Un drone consomme 1 unité d'énergie pour faire 1 pas sur la grille.
	Un drone prend 1 unité de temps pour se déplacer de 1 pas sur la grille.*/
pred dechargerBatterie [ d: Drone, t:Time]
{
	let t' =t.next
	{
		!batterieVide[d,t]=>(d.batterie.t' = add[d.batterie.t, Int[-1]]) else batterieConstante[d,t]
	}
	/*chargeConstante[d,t] and */commandeDroneConstante[d,t] 
}

/* Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */ 
pred chargerCommande [ d:Drone, t:Time]
{
	let t' =t.next
	{
		d.cmd.t'= Entrepot.currentCmd.t && d.charge.t' = #d.cmd.t'.produit 
		&& ( ( Entrepot.currentCmd.t != last) => ( Entrepot.currentCmd.t' = next[Entrepot.currentCmd.t]) else (#Entrepot.currentCmd.t'=0) )
	}
	batterieConstante[d,t] and positionConstante[d,t]
}

/* Une fois le réceptacle rejoint, l'action de livrer les produits prend 1 unité de temps. */
pred livrerProduits [ d: Drone, t:Time]
{	
//	some r:Receptacle |
	let t' =t.next
	{		
	    #d.cmd.t' = 0 && d.charge.t' = Int[0] 
		// ( ( add[r.charge.t, d.charge.t] <=  r.rcap )  => ((r.charge.t' = add[r.charge.t, d.charge.t]) && chargeVide[d,t']) else
		 // ( (r.charge.t' = r.rcap) && (d.charge.t' = sub[d.charge.t, sub[r.rcap, r.charge.t]]) && viderReceptacle[r,t'] ) )
	}
	batterieConstante[d,t] && positionConstante[d,t]
}

pred viderReceptacle [ r:Receptacle, t:Time]
{	
	let t'=t.next
	{
		chargeReceptacleMaximum[r,t] => (r.charge.t' = Int[0])
	}	
}

// Entrepot

/* Un drone peut recharger sa batterie au niveau de l'entrepôt. */	
pred BatterieEntrepot[d: Drone, t:Time] 
{
	(surEntrepot[d,t] && chargeVide[d,t] && !batteriePleine[d,t]) =>  chargerBatterie[d,t] 					
}

/*	Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */
pred ChargementEntrepot[d: Drone, t:Time]
{
	(chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t]) => chargerCommande[d,t] else  commandeEntrepotConstante[d,t]
}

pred progEntrepot[d:Drone ,t:Time]
{
	BatterieEntrepot[d,t] and ChargementEntrepot[d,t] 
}

// Receptacle

/* Un drone interagit avec un réceptacle pour y déposer les produits qu'il porte.	*/
pred LivraisonReceptacle[d: Drone, t:Time] 
{		
	surBonReceptacle[d,t] && !chargeVide[d,t] => livrerProduits[d,t] 	
}

/*	Un réceptacle lambda permet aussi à un drone de recharger sa batterie. */
pred BatterieReceptacle[d: Drone, t:Time] 
{		
	(surReceptacle[d,t]  && !batteriePleine[d,t] ) => chargerBatterie[d,t] 
}

/* Un drone ne peut pas livrer ses produits et recharger sa batterie en même temps */
pred BatterieBonReceptacle[d:Drone,t:Time]
{		
	(surBonReceptacle[d,t] && chargeVide[d,t] && !batteriePleine[d,t] ) => chargerBatterie[d,t]
}

pred progReceptacle[d:Drone ,t:Time]
{
	LivraisonReceptacle[d,t] and BatterieReceptacle[d,t] and BatterieBonReceptacle[d,t]
}

//Faits :

//c'est un invariant, si un drone porte une commande alors sa charge est egale a celle de la commande 
fact ChargeCommande
{
	all d:Drone, t:Time | #d.cmd.t != 0 => (d.charge.t = #d.cmd.t.produit) else d.charge.t = Int[0]

}
