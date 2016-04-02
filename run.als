open signatures
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
run go for 4 but exactly 30 Time, exactly 1 Drone, exactly 4 Position, exactly 3 Commande, exactly 2 Receptacle

check a  for 4 but exactly 15 Time, exactly 1 Drone


/* 

Problème réglé sur les commandes: elles s'enchaînent correctement et un drone ne reprend jamais la même commande 
=> une fois que toutes les commandes ont été livrées, le drone retourne à l'entrepot, se recharge en batterie et ne fait plus rien

A faire : 
	- le fact ChargeCommande est provisoire (je pense qu'il faudra réutiliser les chargeConstante) et il faut modifier le livrerProduits et viderReceptacle ==> il se peut que le nombre de produits soit supérieur à la capacité des charges !
	- c'est traité le comportement du drone s'il est bloqué à un endroit car les positions suivantes sont occupées ? 
	- il faut rendre constante la charge du receptacle quand on ne l'utilise pas
	
	
*/
	
