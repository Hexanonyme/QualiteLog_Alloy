open signatures

//Prédicats :

pred surEntrepot [ d:Drone, t:Time] 
{
	some e:Entrepot | d.pos.t = e.pos
}

pred surReceptacle [ d:Drone , t:Time]
{
	some r:Receptacle | (d.pos.t = r.pos) && (d.pos.t != Entrepot.pos)
}

pred surBonReceptacle [ d:Drone , t:Time]
{
	d.pos.t = d.cmd.t.rec.pos
}

pred enDeplacement [ d:Drone, t:Time]
{
	let t' =t.next
	{
		d.pos.t' != d.pos.t
	}
}

 /* La capacité de la batterie d'un drone est de 3 unités d'énergie */	
pred batteriePleine [d:Drone, t:Time]
{
	d.batterie.t = Int[3]
}

pred batterieVide [d:Drone, t:Time]
{
	d.batterie.t = Int[0]
}

pred chargeVide [ d:Drone, t:Time]
{	
	d.charge.t = Int[0]
}

/* Un drone prend 1 unité de temps pour recharger sa batterie de 1 unité d'énergie */
pred chargerBatterie [ d: Drone, t:Time]
{
	let t' =t.next
	{
		!batteriePleine[d,t] => (d.batterie.t' = add[d.batterie.t, Int[1]]) else batterieConstante[d,t]
	}
}

/* Un drone consomme 1 unité d'énergie pour faire 1 pas sur la grille.
	Un drone prend 1 unité de temps pour se déplacer de 1 pas sur la grille.*/
pred dechargerBatterie [ d: Drone, t:Time]
{
	let t' =t.next
	{
		!batterieVide[d,t]=>(d.batterie.t' = add[d.batterie.t, Int[-1]]) else batterieConstante[d,t]
	}
}

pred batterieConstante [ d: Drone, t:Time]
{
	let t' =t.next
	{
		d.batterie.t' = d.batterie.t
	}
}

/* Une fois le réceptacle rejoint, l'action de livrer les produits prend 1 unité de temps. */
pred livrerProduits [ d: Drone, t:Time]
{	
	some r:Receptacle |
	let t' =t.next
	{		
			!enDeplacement[d,t] && batterieConstante[d,t]  &&
		 ( ( add[r.charge.t, d.charge.t] <=  r.rcap )  => ((r.charge.t' = add[r.charge.t, d.charge.t]) && chargeVide[d,t']) else
		  ( (r.charge.t' = r.rcap) && (d.charge.t' = sub[d.charge.t, sub[r.rcap, r.charge.t]]) && viderReceptacle[r,t'] ) )
	}
}

pred viderReceptacle [ r:Receptacle, t:Time]
{	
	let t'=t.next
	{
		chargeReceptacleMaximum[r,t] => (r.charge.t' = Int[0])
	}	
}

/* Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */ 
pred chargerCommande [ d:Drone, t:Time]
{
	let t' =t.next
	{
		some e:Entrepot | d.cmd.t'= e.currentCmd.t && e.currentCmd.t' = next[e.currentCmd.t] && d.charge.t' = #d.cmd.t'.produit 
	}
}

pred chargeConstante [ d: Drone, t:Time]
{
	let t' =t.next
	{
		d.charge.t' = d.charge.t
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

pred peutBouger{}

// Entrepot

/* Un drone peut recharger sa batterie au niveau de l'entrepôt. */	
pred BatterieEntrepot[d: Drone, t:Time] 
{
	(surEntrepot[d,t] && chargeVide[d,t] && !batteriePleine[d,t]) => ( chargerBatterie[d,t] && !enDeplacement[d,t] && chargeConstante[d,t])								
}

/*	Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */
pred ChargementEntrepot[d: Drone, t:Time]
{
	(chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t]) => chargerCommande[d,t] && !enDeplacement[d,t] && batterieConstante[d,t]
}

pred QuitterEntrepot[d: Drone, t:Time]
{
	((peutBouger && !chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t] ) => (enDeplacement[d,t] && chargeConstante[d,t])) and
	((!peutBouger && !chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t] ) => (!enDeplacement[d,t] && chargeConstante[d,t] && batterieConstante[d,t] ))
}

pred progEntrepot[d:Drone ,t:Time]
{
	BatterieEntrepot[d,t] and ChargementEntrepot[d,t] and QuitterEntrepot[d,t]
}

// Receptacle

/* Un drone interagit avec un réceptacle pour y déposer les produits qu'il porte.	*/
pred LivraisonReceptacle[d: Drone, t:Time] 
{		
	(surBonReceptacle[d,t] && !chargeVide[d,t] )=> livrerProduits[d,t]
}

/*	Un réceptacle lambda permet aussi à un drone de recharger sa batterie. */
pred BatterieReceptacle[d: Drone, t:Time] 
{		
	(surReceptacle[d,t]  && !batteriePleine[d,t] ) => (chargerBatterie[d,t] && !enDeplacement[d,t]&& chargeConstante[d,t])
}

/* Un drone ne peut pas livrer ses produits et recharger sa batterie en même temps */
pred BatterieBonReceptacle[d:Drone,t:Time]
{		
	(surBonReceptacle[d,t] && chargeVide[d,t] && !batteriePleine[d,t] ) => (chargerBatterie[d,t] && !enDeplacement[d,t] && chargeConstante[d,t])
}

pred QuitterReceptacle[d:Drone,t:Time] 
{		
	((peutBouger && batteriePleine[d,t] && surReceptacle[d,t]) =>  (enDeplacement[d,t] && chargeConstante[d,t])) and
	((!peutBouger && batteriePleine[d,t] && surReceptacle[d,t]) =>  (!enDeplacement[d,t] && batterieConstante[d,t] && chargeConstante[d,t]))
}

pred progReceptacle[d:Drone ,t:Time]
{
	LivraisonReceptacle[d,t] and BatterieReceptacle[d,t] and BatterieBonReceptacle[d,t] and QuitterReceptacle[d,t]
}

// ni Entrepot ni Receptacle

pred Deplacement[d: Drone, t:Time]
{
	(enDeplacement[d,t] => (dechargerBatterie[d,t] && chargeConstante[d,t] )) and
	((!enDeplacement[d,t] && !surReceptacle[d,t] && !surEntrepot[d,t])=>batterieConstante[d,t] && chargeConstante[d,t])
}

//Faits :

/*fact traces 
{
	init [first]
    all t: Time-last
    {
		all d : Drone |  progEntrepot[d,t] and Deplacement[d,t] and progReceptacle[d,t] 
	}
}*/

//Assertions :
