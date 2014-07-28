/*
*Importando a library ordering. Em seguida, aplicando à assinatura Time.
*/

open util/ordering [Time] 

module NinjAlarm

/** NinjAlarm 

Alarme especialmente desenvolvido para pessoas com problemas para acordar, a proposta
do aplicativo é que o usuario tenha que apertar um botao que se move continuamente na 	tela 
forçando o a despertar para poder desligar o alarme.

*/

/**ASSINATURAS*/


/*
*Assinatura para simular tempo
*/
sig Time{}

/*
*Assinatura que contem e gerencia todos os alarmes
*/
one sig MyAlarms{
	alarms: Alarm set -> Time
}

/*
* Representa os alarmes
*/
abstract sig Alarm{
	button: StopButton one ->  Time
}

/*
* Representa um tipo de Alarm, possui tipo de button e uma ou mais datas
*/
sig  AlarmByWeekDay extends Alarm{
	day:  Day some -> Time
}

/*
* Representa um tipo de Alarm, possui tipo de button e uma data
*/
sig AlarmByDate extends Alarm{
	date:  Date one -> Time
}

/*
* Representa o botao que tem diferentes difilcudades
*/
abstract sig StopButton{}

/*
* Representa a Dificuldade do botao
*/
one sig Normal, Hard, Ninja extends StopButton{}

/*
* Representa quando o alarme vai tocar
*/
sig Date{}

/*
* Representa quando o alarme por dia vai tocar
*/
sig Day{}

/*
fact Untied{
	all a: Alarm  | a in MyAlarms.alarms

}*/

pred show[]{}

/**PREDICADOS*/


pred init[t: Time]{}

/**1: Predicados que servem ao propósito de simular o comportamento temporal do sistema*/

pred editAlarmDate[t, t' : Time, a: AlarmByDate, d: Date]{
	a in MyAlarms.alarms.t
	a.date.t != d
	a.date.t' = d
}

pred editAlarmDay[t, t' : Time, a: AlarmByWeekDay, d: Day]{
	a in MyAlarms.alarms.t
	a.day.t !=  d
	a.day.t' = d
}

pred addAlarm[t, t' : Time, a: Alarm]{
	a !in MyAlarms.alarms.t
	MyAlarms.alarms.t' = MyAlarms.alarms.t + a	
}

pred rmAlarm[t, t' : Time, a: Alarm]{
	a in MyAlarms.alarms.t
	MyAlarms.alarms.t' = MyAlarms.alarms.t - a	
}

pred changeButton[t, t' : Time, a: Alarm, b: StopButton]{
	b !in a.button.t 
	a.button.t' = b
}

fact traces {
	init [first]
	all pre: Time - last | let pos = pre.next |
	some a: Alarm , d: Date, d1: Day, b: StopButton |
	editAlarmDate[pre,pos,a, d] or
	editAlarmDay[pre,pos,a, d1] or
	addAlarm[pre,pos, a] or
	rmAlarm[pre,pos, a] or
	changeButton[pre, pos, a, b]

}

run show for 5
