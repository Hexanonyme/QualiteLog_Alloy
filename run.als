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
run go for 4 but exactly 15 Time, exactly 1 Drone, exactly 4 Position, exactly 3 Commande, exactly 2 Receptacle

check a  for 4 but exactly 15 Time, exactly 1 Drone


/* 

Attention : le run marche avec cette config mais pas si on met un Time supérieur ou une seule Commande ==> problème du next sur commande
	
A faire : 
	- il faut faire attention à l'utilisation de next sur Commande ==> faire comme pour Time, vérifier qu'on n'en soit pas à la dernière commande sinon le next pose un gros soucis !!!
	- le fact ChargeCommande est provisoire (je pense qu'il faudra réutiliser les chargeConstante) et il faut modifier le livrerProduits et viderReceptacle ==> il se peut que le nombre de produits soit supérieur à la capacité des charges !
	- c'est traité le comportement du drone s'il est bloqué à un endroit car les positions suivantes sont occupées ? 
	- il faut rendre constantes les charges du receptacle et de l'entrepot quand on ne les utilise pas
	- c'est géré le fait qu'une commande une fois livrée ne puisse plus être chargée à l'entrepôt ? à voir
	
*/
	
