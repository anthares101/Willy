Distribuci�n de "Willy en el espacio" 
======================================
Pr�cticas de Sistemas Inteligentes (Grado en Ingenier�a Inform�tica, UCO)
Por: Carlos Garc�a Mart�nez, Manuel Jes�s Mar�n Jim�nez y Amelia Zafra G�mez 
======================================
Realizadas por: �ngel Heredia P�rez y Sergio G�mez Morales

Willy es un astronauta que se encuentra perdido en el espacio, y quiere llegar a la Tierra. Para
ello deber� ir recorriendo el espacio a su alrededor hasta encontrarla, pero una serie de peligros
pueden hacer que nunca llegue a ella. Por suerte, estos peligros emiten una se�al a su alrededor
que Willy puede detectar para evitarlos: el Alien emite ruido y los Agujeros negros emiten
atracci�n. Willy adem�s cuenta con un ca��n l�ser en su nave con el que puede disparar al Alien,
pero solo cuenta con un tiro.

Este proyecto lo hemos dividido en tres m�dulos principales que van iterando entre s�.

El primer m�dulo es el de percepci�n, y se encarga de que Willy detecte lo su posici�n actual y si
lo que hay alrededor puede o no ser peligroso.

El segundo m�dulo es el de inferencia, con el cual Willy puede inferir peligros a partir de la
informaci�n extra�da del m�dulo anterior. Es el m�dulo con m�s l�neas de c�digo para asegurarnos
de que Willy tiene muchas formas de inferir en distintas situaciones.

El tercer m�dulo es el de movimiento, utiliza las inferencias realizadas anteriormente para
realizar movimientos, en algunos casos estrat�gicos. Por lo general, Willy se mover� libremente si
no detecta peligros, si detecta que cerca hay un Agujero negro, volver� hacia atr�s evit�ndolo a
toda costa, y si detecta un Alien, se mover� de forma que pueda detectar su posici�n exacta para
luego dispararle.

Ejecucion:
======================================
-Copia el contenido del directorio correspondiente a tu sistema operativo en el mismo directorio donde se encuentre el fichero "WillyDemo.jar"
-Escribir en el terminal: java -Djava.library.path=. -jar WillyDemo.jar
-Para cargar los mapas de validacion se le a�adir� la flag: -maps maps_validation 
-Para que el usuario sea el que juegue: -interactive
-Si se pulsa "All maps" se empezar� a resolver todos los mapas del directorio "maps"
