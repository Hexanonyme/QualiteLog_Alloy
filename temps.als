open signatures
open carte

//Faits
pred setCommande  [t: Time, d: Drone]
{
	d.pos.t = Entrepot.pos and #d.cmd = 0/* and d.batterie.t = Int[3]*/ => Entrepot.currentCmd.t = next[Entrepot.currentCmd.t]/*	and d.cmd.t = Entrepot.currentCmd.t
*/}

//Prédicats
pred init [t:Time]
{
	all d : Drone, r:Receptacle | d.pos.t = Entrepot.pos 
	&& d.batterie.t = Int[1] 
	&& d.charge.t =Int[0] 
	&& r.charge.t = Int[0] 
	&& #d.cmd = 0 
	&& Entrepot.currentCmd.t = first
}

pred arretSurReceptacleBatterieVide[t: Time, d: Drone] 
{
	eq[d.batterie.t, 0] => eq[d.pos.t.isReceptacle, 1]
}

pred arretSurReceptacle[t, t': Time, d: Drone] 
{
	eq[d.batterie.t, 0] => eq[d.pos.t.isReceptacle, 1]
}


pred interdictionSaut  [t, t': Time, d: Drone]
{
	#d.cmd = 0 => d.pos.t' = d.pos.t else
	(d.pos.t' = d.pos.t.nord or d.pos.t' = d.pos.t.est or d.pos.t' = d.pos.t.sud or d.pos.t' = d.pos.t.ouest)
}


pred moveDrone [t, t': Time, d: Drone] 
{
	let dest = destination[d, t],
	 newPos = closer [d.pos.t.nord, d.pos.t.est, d.pos.t.sud, d.pos.t.ouest, dest]
	{
		d.pos.t' = newPos
	}
}

fact traces 
{
	init [first]
    all t: Time-last | let t' = t.next
    {
		all d : Drone |  arretSurReceptacleBatterieVide[t, d] and interdictionSaut[t, t', d] and setCommande[t, d] and
			(eq[d.pos.t.isReceptacle, 0] => moveDrone [t, t', d] or arretSurReceptacle [t, t', d] )
	}
}

pred progTemps
{
	
}

//Fonctions
fun closer [e1, e2, e3, e4, dest: Position] : Position
{
	let a = manhattan[e1, dest], 
		  b = manhattan[e2, dest], 
		  c = manhattan[e3, dest], 
		  d = manhattan[e4, dest], 
		  smallerManhattan = 	smaller [smaller [a, b], smaller [c, d] ] 
	|
		eq[smallerManhattan, a] => e1 else
		eq[smallerManhattan, b] => e2 else
		eq[smallerManhattan, c]=> e3 else
		e4
}

fun destination [d: Drone, t : Time] : Position
{
	#d.cmd.t= 1 => d.cmd.t.rec.pos else Entrepot.pos
}
