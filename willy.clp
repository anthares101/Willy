;*****************************************
; Autores:
; Historial de cambios:
;  - Fecha: mejoras/cambios
;*****************************************

(defrule MAIN::passToMyMAIN
	=>
	(focus myMAIN))


;==========================================
(defmodule myMAIN (import MAIN deftemplate ?ALL) (import InternalFunctions deffunction ?ALL) (export deftemplate ?ALL))

(deftemplate casilla
	(slot x)
	(slot y)
	(slot visited (default 0))
	(slot safe (default 0))
	(slot alien (default 0))
	(slot hole (default 0))
	(slot pull)
	(slot noise)
)
(deftemplate willy
	(slot x)
	(slot y)
)
(defrule firstState
	(not (casilla (x ?)(y ?) (visited ?) (safe ?) (alien ?) (hole ?) (pull ?) (noise ?)))
=>
	(assert (casilla (x 0)(y 0) (visited 1) (safe 1) (alien 0) (hole 0) (pull 0) (noise 0)))
	(assert (willy (x 0) (y 0)))
)

(defrule direction
	(directions $? ?direction $?)
=>
	(assert (dir ?direction))
)

(defrule convertionNorth
	?h1<-(dir north)
=>
	(retract ?h1)
	(assert (y 1))
)

(defrule convertionSouth
	?h1<-(dir south)
=>
	(retract ?h1)
	(assert (y -1))
)

(defrule convertionEast
	?h1<-(dir east)
=>
	(retract ?h1)
	(assert (x 1))
)

(defrule convertionWest
	?h1<-(dir west)
=>
	(retract ?h1)
	(assert (x -1))
)
;=====================================
; Se pueden crear otros módulos (siempre que lo acepte el programa) con el contenido que se desee
; Se deben especificar las indicaciones de importación y exportación que deseeis, pero se sugiere importar todo de MAIN y de vuestro myMAIN
; Ejemplo:
(defmodule Modulo1 (import MAIN deftemplate ?ALL) (import myMAIN deftemplate ?ALL))

; Se puede crear cualquier constructor que deseis y que lo acepte el programa (funciones, plantillas, reglas...)





;=========================================
; Otros módulos (tantos como se deseen)
