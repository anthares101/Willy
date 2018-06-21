Distribución de "Willy en el espacio" 
======================================
Prácticas de Sistemas Inteligentes (Grado en Ingeniería Informática, UCO)
Por: Carlos García Martínez, Manuel Jesús Marín Jiménez y Amelia Zafra Gómez 
======================================
Realizadas por: Ángel Heredia Pérez y Sergio Gómez Morales

Willy es un astronauta que se encuentra perdido en el espacio, y quiere llegar a la Tierra. Para
ello deberá ir recorriendo el espacio a su alrededor hasta encontrarla, pero una serie de peligros
pueden hacer que nunca llegue a ella. Por suerte, estos peligros emiten una señal a su alrededor
que Willy puede detectar para evitarlos: el Alien emite ruido y los Agujeros negros emiten
atracción. Willy además cuenta con un cañón láser en su nave con el que puede disparar al Alien,
pero solo cuenta con un tiro.

Este proyecto lo hemos dividido en tres módulos principales que van iterando entre sí.

El primer módulo es el de percepción, y se encarga de que Willy detecte lo su posición actual y si
lo que hay alrededor puede o no ser peligroso.

El segundo módulo es el de inferencia, con el cual Willy puede inferir peligros a partir de la
información extraída del módulo anterior. Es el módulo con más líneas de código para asegurarnos
de que Willy tiene muchas formas de inferir en distintas situaciones.

El tercer módulo es el de movimiento, utiliza las inferencias realizadas anteriormente para
realizar movimientos, en algunos casos estratégicos. Por lo general, Willy se moverá libremente si
no detecta peligros, si detecta que cerca hay un Agujero negro, volverá hacia atrás evitándolo a
toda costa, y si detecta un Alien, se moverá de forma que pueda detectar su posición exacta para
luego dispararle.

Ejecucion:
======================================
-Copia el contenido del directorio correspondiente a tu sistema operativo en el mismo directorio donde se encuentre el fichero "WillyDemo.jar"
-Escribir en el terminal: java -Djava.library.path=. -jar WillyDemo.jar
-Para cargar los mapas de validacion se le añadirá la flag: -maps maps_validation 
-Para que el usuario sea el que juegue: -interactive
-Si se pulsa "All maps" se empezará a resolver todos los mapas del directorio "maps"
