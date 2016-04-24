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

pred commandeDejaChargee [d:Drone, t:Time]
{
	let t' = t.next
	{
		some d1 : Drone | d1 != d &&  d1.cmd.t' =  Entrepot.currentCmd.t 
	}
}

/* Un drone prend 1 unité de temps pour recharger sa batterie de 1 unité d'énergie */
pred chargerBatterie [ d: Drone, t:Time]
{
	let t' =t.next
	{
		d.batterie.t' = add[d.batterie.t, Int[1]]
	}
	commandeDroneConstante[d,t] and positionConstante[d,t]
}

/* Un drone consomme 1 unité d'énergie pour faire 1 pas sur la grille.
	Un drone prend 1 unité de temps pour se déplacer de 1 pas sur la grille.*/
pred dechargerBatterie [ d: Drone, t:Time]
{
	let t' =t.next
	{
		d.batterie.t' = add[d.batterie.t, Int[-1]]
	}
	commandeDroneConstante[d,t] 
}

/* Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */ 
pred chargerCommande [ d:Drone, t:Time]
{
	let t' =t.next
	{
	 	d.cmd.t'= Entrepot.currentCmd.t && d.charge.t' = #d.cmd.t'.produit &&
		(( Entrepot.currentCmd.t != last) => ( Entrepot.currentCmd.t'= next[Entrepot.currentCmd.t]) else (#Entrepot.currentCmd.t'=0))
	}
	batterieConstante[d,t] and positionConstante[d,t]
}

/* Une fois le réceptacle rejoint, l'action de livrer les produits prend 1 unité de temps. */
pred livrerProduits [ d: Drone, t:Time]
{	
   	let t' =t.next
	{		
		chargeVide[d,t'] && #d.cmd.t' = 0
	}
	batterieConstante[d,t] && positionConstante[d,t]
}

// Entrepot

/* Un drone peut recharger sa batterie au niveau de l'entrepôt. */	
pred batterieEntrepot[d: Drone, t:Time] 
{
	(surEntrepot[d,t] && chargeVide[d,t] && !batteriePleine[d,t]) =>  chargerBatterie[d,t] 					
}

/*	Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */
pred chargementEntrepot[d: Drone, t:Time]
{
	(chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t] && !commandeDejaChargee[d,t]) => chargerCommande[d,t]
	else (batterieConstante[d,t] and positionConstante[d,t]) //commandeEntrepotConstante[d,t]
}

pred progEntrepot[d:Drone ,t:Time]
{
	batterieEntrepot[d,t] and chargementEntrepot[d,t] 
}

// Receptacle

/* Un drone interagit avec un réceptacle pour y déposer les produits qu'il porte.	*/
pred livraisonReceptacle[d: Drone, t:Time] 
{		
	(surBonReceptacle[d,t] && !chargeVide[d,t]) => livrerProduits[d,t] 	
}

/*	Un réceptacle lambda permet aussi à un drone de recharger sa batterie. */
pred batterieReceptacle[d: Drone, t:Time] 
{		
	(surReceptacle[d,t]  && !batteriePleine[d,t] ) => chargerBatterie[d,t] 
}

/* Un drone ne peut pas livrer ses produits et recharger sa batterie en même temps */
pred batterieBonReceptacle[d:Drone,t:Time]
{	
	(surBonReceptacle[d,t] && chargeVide[d,t] && !batteriePleine[d,t] ) => chargerBatterie[d,t]
}

pred progReceptacle[d:Drone ,t:Time]
{
	livraisonReceptacle[d,t] and batterieReceptacle[d,t] and batterieBonReceptacle[d,t]
}

pred progCharges[d:Drone , t:Time]
{
	progEntrepot[d,t] and progReceptacle[d,t] 
}

//Faits :

// Le nombre de produits d'une commande ne doit pas dépasser dcap et rcap 
fact NombreProduits
{
	all d : Drone, r : Receptacle, c : Commande | (#c.produit <= d.dcap) && (#c.produit <=r.rcap)
}

// La charge d'un drone doit rester constante à part quand il charge la commande ou quand il livre des produits 
fact ChargeCommande
{
	all d:Drone, t:Time-last |	(!chargerCommande[d,t] && !livrerProduits[d,t] ) => chargeConstante[d,t]
}
