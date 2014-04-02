/*
*Importando a library ordering. Em seguida, aplicando à assinatura Time.
*/
open util/ordering [Time]


/** Sistema de Monitoramento de Pacientes (Cliente - Kaio)

Trata-se de um sistema onde profissionais da saúde monitoram pacientes cadastrados. Este software 
utiliza a plataforma Linux para o servidor e a plataforma cliente será qualquer sistema que tenha acesso
 a internet com um navegador web. Por meio de uma conexão de rede ethernet, os pacientes se 
comunicam com o servidor com um nome de usuário e uma senha e registram seus sintomas diários.
 Para os pacientes se cadastrarem precisam fornecer: Nome completo data de nascimento, e-mail, etc.
 Cada médico tem uma senha particular para acesso ao software e monitoram 1 a 3 pacientes.
 O sistema possui 2 gerentes que são os responsáveis por adicionar os médicos e acionar o suporte
 ( por e-mail, telefone, etc.) caso haja algum erro no sistema.

*/

module AssistenciaHospitalar

-- Existem varios sistemas
-- Os sistemas tem que estar conectado a internet ou nao
-- O sistema vai ter uma linha com o paciente e vai ter que checar se o paciente tem acesso ao servidor
-- O gerente vai ser um medico, e sao imutaveis
-- Cada médico pode ter no maximo 3 pacientes
-- O estado do sistema so pode mudar pra com acesso, se anteriormente ele estiver sem acesso
/**ASSINATURAS*/

/*
*Assinatura para simular tempo
*/
sig Time{}

/*
Servidor é onde vai ficar contido os dados da aplicação (medicos e pacientes que estão cadastrados no sistema), respondendo 
a requisição dos sistemas dos pacientes cadastrados. Este servidor tem que rodar em Linux. O servidor terá obrigatoriamente
dois gerentes que, necessariamente, devem ser médicos e serão responsáveis por cadastrar novos médicos e acionar o suporte.
*/
one sig Servidor{
	gerentes: some Medico,
	medicos:  some Medico,
	pacientes: set Paciente,
	plataformaServidor: one Linux,
	suporte:  Suporte lone -> Time
}

/*
Vão ser os clientes da nossa aplicação, eles vão ter um sistema cliente (em qualquer platarforma) que tenha acesso à internet
para poder se comunicar com o servidor. Além disso, eles podem estar ou não cadastrados no servidor.
*/
sig Paciente{
	data: lone DataDeNascimento,
	nomePaciente: lone Nome,
	sintomas: set Sintoma,
	emailPaciente: lone Email,
	loginPaciente: lone Login,
	senhaPaciente: lone Senha,
	sistemaPaciente: lone SistemaCliente,
	statusCliente:one StatusCadastro
}

/*
São os médicos que monitorarão os pacientes cadastrados. Cada médico poderá monitorar de 1 a 3 pacientes. O médico pode 
estar ou não cadastrado no servidor.
*/
sig Medico{
	pacientes: some Paciente,
	senhaMedico: lone Senha,
	nomeMedico: lone Nome,
	emailMedico: lone Email,
	loginMedico: lone Login,
	statusMedico: one StatusCadastro
}

/*
Sistema utilizado pelos clientes, que serão os pacientes, para registrar seus sintomas diários. Deverá ser composto por qualquer
plataforma. Para utilizar o sistema, ele deverá estar conectado à internet.
*/
sig SistemaCliente{
	internet: one StatusInternet,
	plataforma: one SistemaOperacional
}

sig Suporte{}
/*
abstract sig StatusAcionado{}

sig SuporteAcionado, SuporteNaoAcionado extends StatusAcionado{}
*/
abstract sig StatusCadastro{}

sig Cadastrado, NaoCadastrado extends StatusCadastro{}

abstract sig StatusInternet{}

sig ComInternet, SemInternet extends StatusInternet{}

abstract sig SistemaOperacional{}

one	sig Linux extends SistemaOperacional{}

sig Senha{}

sig Login{}

sig Nome{}	

sig Email{}

sig DataDeNascimento{}

sig Sintoma{}

/**FUNÇÕES UTILITÁRIAS USADAS EM VÁRIAS SEÇÕES DO CÓDIGO*/

fun pacientesNoServidor[s: Servidor]: set Paciente{
	s.pacientes
}

fun medicosNoServidor[s: Servidor]: set Medico{
	s.medicos
}

fun todosOsNomes[p: Paciente, m: Medico]: set Nome{
	 p.nomePaciente + m.nomeMedico
}

/**PREDICADOS*/

pred cadaMedicoTemDe1a3Pacientes[]{
	all m1:Medico | #m1.pacientes < 3
}

pred todoSistemaClienteEstaEmPaciente[]{
	all s:SistemaCliente, p:Paciente | s in p.sistemaPaciente
}

pred oSistemaTem2GerentesDiferentes[]{
	all s1:Servidor | #s1.gerentes = 2
	all g1:Servidor.gerentes, g2: Servidor.gerentes - g1 | g1 != g2
}

pred loginsDevemSerDiferentes[]{
	all p1:Paciente, p2:Paciente-p1 | p1.loginPaciente != p2.loginPaciente
	all m1:Medico, m2:Medico-m1 | m1.loginMedico != m2.loginMedico
	all m1:Medico, p1:Paciente| m1.loginMedico != p1.loginPaciente
}

pred emailsDevemSerDiferentes[]{
	all p1:Paciente, p2:Paciente-p1 | p1.emailPaciente != p2.emailPaciente
	all m1:Medico, m2:Medico-m1 | m1.emailMedico != m2.emailMedico
	all m1:Medico, p1:Paciente| m1.emailMedico != p1.emailPaciente
}

pred pacientesEMedicosDevemEstarNoServidor[]{
	all p1:Paciente |  p1 in pacientesNoServidor[Servidor]
	all m: Medico | m in medicosNoServidor[Servidor]
}

pred medicoPodeTerPacientes[]{
	all m: Medico, p: Paciente | ((m.statusMedico = Cadastrado) and (p.statusCliente = Cadastrado)) <=> p in m.pacientes
}

pred pacientePodeTerMedicos[]{
	all m: Medico, p: Paciente | p in m.pacientes  => p.statusCliente = Cadastrado
}

pred cadastradosPossuemTodosOsDados[]{
	all p: Paciente | p.statusCliente = Cadastrado => #p.loginPaciente = 1
	all p: Paciente | p.statusCliente = Cadastrado => #p.senhaPaciente = 1
	all p: Paciente | p.statusCliente = Cadastrado => #p.emailPaciente = 1
	all p: Paciente | p.statusCliente = Cadastrado => #p.nomePaciente = 1
	all p: Paciente | p.statusCliente = Cadastrado => #p.data = 1
	all p: Paciente | p.statusCliente = Cadastrado => #p.sistemaPaciente = 1

	all p: Medico | p.statusMedico = Cadastrado => #p.loginMedico = 1
	all p: Medico | p.statusMedico = Cadastrado => #p.senhaMedico = 1
	all p: Medico | p.statusMedico= Cadastrado => #p.emailMedico = 1
	all p:Medico| p.statusMedico = Cadastrado => #p.nomeMedico= 1
}

pred naoCadastradosNaoPossuemTodosOsDados[]{
	all p: Paciente | p.statusCliente = NaoCadastrado => #p.loginPaciente = 0
	all p: Paciente | p.statusCliente = NaoCadastrado => #p.senhaPaciente = 0
	all p: Paciente | p.statusCliente = NaoCadastrado => #p.emailPaciente = 0
	all p: Paciente | p.statusCliente = NaoCadastrado => #p.nomePaciente = 0
	all p: Paciente | p.statusCliente = NaoCadastrado => #p.data = 0
	all p: Paciente | p.statusCliente = NaoCadastrado => #p.sintomas = 0
	all p: Paciente | p.statusCliente = NaoCadastrado => #p.sistemaPaciente = 0

	all p: Medico | p.statusMedico = NaoCadastrado => #p.loginMedico = 0
	all p: Medico | p.statusMedico = NaoCadastrado => #p.senhaMedico = 0
	all p: Medico | p.statusMedico= NaoCadastrado => #p.emailMedico = 0
	all p:Medico| p.statusMedico = NaoCadastrado => #p.nomeMedico= 0
}

pred acionaSuporte[t, t' : Time, su: Suporte, se: Servidor ]{
	no se.suporte.t
	se.suporte.t' = su
}

pred removeSuporte[t, t' : Time, su: Suporte, se: Servidor ]{
	se.suporte.t = su
	no se.suporte.t'
}

pred cadastrarMedico[]{}

pred cadastrarSintoma[]{}

pred init[t: Time]{
	no Servidor.suporte.t
}

pred show[]{}

/**FATOS*/

fact EspecificacaoDoSistema{
	cadaMedicoTemDe1a3Pacientes
	todoSistemaClienteEstaEmPaciente
	oSistemaTem2GerentesDiferentes
	loginsDevemSerDiferentes
	emailsDevemSerDiferentes
	pacientesEMedicosDevemEstarNoServidor
	medicoPodeTerPacientes
 	pacientePodeTerMedicos
	cadastradosPossuemTodosOsDados
	naoCadastradosNaoPossuemTodosOsDados
// fatos do nome, senha, login, email, statusCadastrado, data, sintomas
	qualquerDadoPertenceAalguem
	suporteDeveEstarNoServidor
	oStatusDaInternetDeveEstarDentroDoSistemaCliente
	
}

fact fatosNome{
	all n:Nome | n in todosOsNomes[Paciente, Medico]
}

fact fatosSuporte{
	all su:Suporte, t: Time | su in Servidor.suporte.t
}

/*
fact fatosStatusSuporte{
	all su: Suporte,  st: StatusAcionado, t: Time | st in su.(statusDoSuporte.t)
}
*/

fact fatosStatusInternet{
	all s: SistemaCliente, st: StatusInternet | st in s.internet
}

fact fatosStatusCadastro{
	all p: Paciente, m : Medico, st: StatusCadastro | st in p.statusCliente or st in m.statusMedico
}

fact fatosSenha{
	all s:Senha | s in Paciente.senhaPaciente + Medico.senhaMedico
}

fact fatosLogin{
	all l:Login | l in Paciente.loginPaciente + Medico.loginMedico
}

fact fatosDataDeNascimento{
	all d:DataDeNascimento | d in Paciente.data
}

fact fatosEmail{
	all e:Email | e in Paciente.emailPaciente + Medico.emailMedico
}

fact fatosSintomas{
	all si:Sintoma | si in Paciente.sintomas
}

fact traces {
	init [first]
	all pre: Time - last | let pos = pre.next |
	some su: Suporte, se: Servidor  |
	acionaSuporte[pre, pos, su, se]
}

run show for 5
