open signatures
open charges2
open carte
open temps
pred prog 
{
	progCarte and progTemps
}

assert  a
{
	prog => all p : Position | Entrepot.pos = p
}

pred go{ prog }
run go for 3 but exactly 10 Time, exactly 1 Drone, exactly 6 Position, exactly 2 Commande

check a  for 5 but exactly 7 Time, exactly 1 Drone

/* LivraisonReceptacle ne marche pas avec la politique du moveDrone actuel ==> revoir les conditions avant
	il ne reste pas sur le receptacle pour livrer et part tout de suite*/
