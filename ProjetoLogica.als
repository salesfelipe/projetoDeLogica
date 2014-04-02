/*
*Importando a library ordering. Em seguida, aplicando Ã  assinatura Time.
*/

open util/ordering [Time]

module AssistenciaHospitalar

/** Sistema de Monitoramento de Pacientes (Cliente - Kaio)

Trata-se de um sistema onde profissionais da saÃºde monitoram pacientes cadastrados. Este software 
utiliza a plataforma Linux para o servidor e a plataforma cliente serÃ¡ qualquer sistema que tenha acesso
 a internet com um navegador web. Por meio de uma conexÃ£o de rede ethernet, os pacientes se 
comunicam com o servidor com um nome de usuÃ¡rio e uma senha e registram seus sintomas diÃ¡rios.
 Para os pacientes se cadastrarem precisam fornecer: Nome completo data de nascimento, e-mail, etc.
 Cada mÃ©dico tem uma senha particular para acesso ao software e monitoram 1 a 3 pacientes.
 O sistema possui 2 gerentes que sÃ£o os responsÃ¡veis por adicionar os mÃ©dicos e acionar o suporte
 ( por e-mail, telefone, etc.) caso haja algum erro no sistema.

*/

-- Existem varios sistemas
-- Os sistemas tem que estar conectado a internet ou nao
-- O sistema vai ter uma linha com o paciente e vai ter que checar se o paciente tem acesso ao servidor
-- O gerente vai ser um medico, e sao imutaveis
-- Cada mÃ©dico pode ter no maximo 3 pacientes
-- O estado do sistema so pode mudar pra com acesso, se anteriormente ele estiver sem acesso

/**ASSINATURAS*/

/*
*Assinatura para simular tempo
*/

sig Time{}

/*
O servidor eh onde vai ficar contido os dados da aplicacao (medicos e pacientes que estao cadastrados no sistema), respondendo 
a requisicao dos sistemas dos pacientes cadastrados. Este servidor tem que rodar em Linux. O servidor terÃ¡ obrigatoriamente
dois gerentes que, necessariamente, devem ser medicos e serao responsaveis por cadastrar novos medicos e acionar o suporte 
quando necessario.
*/
one sig Servidor{
	gerentes: some Medico,
	plataformaServidor: one Linux,
	suporte: one Suporte,
	pacientesCadastrados: set Paciente,
	medicos: set Medico
}

/*
Vao ser os clientes da nossa aplicacao. Eles vao ter um sistema cliente (em qualquer platarforma) que tenha acesso a  internet
para poder se comunicar com o servidor. Alem disso, eles podem estar ou nao cadastrados no servidor dependendo do tempo.
*/
sig Paciente{
	data: one DataDeNascimento,
	nomePaciente: one Nome,
	sintomas: Sintoma -> Time,
	emailPaciente: one Email,
	loginPaciente: one Login,
	senhaPaciente: one Senha,
	sistemaPaciente: one SistemaCliente,
	statusPaciente: StatusCadastro one -> Time
}

/*
Medicos cadastrados devem monitorar de 1 a 3 pacientes e os nao cadastrados devem ter nenhum paciente. O medico podera mudar
de nao cadastrado para cadastrado dependendo do tempo
*/
sig Medico{
	pacientes: Paciente -> Time,
	senhaMedico: one Senha,
	nomeMedico: one Nome,
	emailMedico: one Email,
	loginMedico: one Login,
	statusMedico:  StatusCadastro one -> Time
}

/*
Sistema utilizado pelos pacientes, para registrar seus sintomas diarios. Poderao estar em qualquer outra plataforma, incluindo o 
Linux. Para acessar o servidor, o sistema do paciente devera estar conectado a  internet.
*/
sig SistemaCliente{
	internet: one StatusInternet,
	plataforma: one SistemaOperacional
}

/*
O suporte Ã© acionado exclusivamente pelos gerentes do servidor caso haja algum erro com o mesmo.
*/
sig Suporte{
	statusDoSuporte: StatusAcionado one -> Time
}

abstract sig StatusAcionado{}

one sig SuporteAcionado, SuporteNaoAcionado extends StatusAcionado{}


/*
Status do cadastro dos pacientes e dos mÃ©dicos, que podem estar ou nÃ£o cadastrados no servidor de acordo com o tempo.
*/
abstract sig StatusCadastro{}

sig Cadastrado, NaoCadastrado extends StatusCadastro{}

/*
Refere-se ao status da conexÃ£o do paciente, que precisa estar conectado a Internet para ter acesso ao sistema.
*/
abstract sig StatusInternet{}

sig ComInternet, SemInternet extends StatusInternet{}

/*
Refere-se ao Sistema Operacional que qualquer sistema do paciente podera rodar. JÃ¡ o servidor Ã© representado apenas pelo Linux. 
*/
abstract sig SistemaOperacional{}

// unico SO que Ã© obrigatorio que tenha
one	sig Linux extends SistemaOperacional{}

/*
Senha necessaria a medicos e pacientes para ter acesso ao sistema
*/
sig Senha{}

/*
Login dos medicos e pacientes para logar no sistema
*/
sig Login{}

/*
Nomes dos medicos e pacientes para serem cadastrados
*/
sig Nome{}	

/*
e-mail que eh necessario para o cadastro do pacientes
*/
sig Email{}

/*
Data de nascimento que eh requirida no momento do cadastro do paciente
*/
sig DataDeNascimento{}

/*
Sintoma que o paciente cadastra no sistema. Exclusivo de pacientes.
*/
sig Sintoma{}

/**FUNÃÃES UTILITÃRIAS USADAS EM VÃRIAS SEÃÃES DO CÃDIGO*/

/*
 A funcao retorna o conjunto de pacientes total que estao no servidor
*/
fun pacientesNoServidor[s: Servidor]: set Paciente{
	s.pacientesCadastrados
} 

/*
A funcao retorna o conjunto de medicos total que estao no servidor
*/
fun medicosNoServidor[s: Servidor]: set Medico{
	s.medicos
}

/*
A funcao retorna os nomes de medicos e pacientes cadastrados no servidor
*/
fun todosOsNomes[p: Paciente, m: Medico]: set Nome{
	 p.nomePaciente + m.nomeMedico
}

/**PREDICADOS*/

/*
Todo medico so pode se relacionar com pacientes que estao cadastrados e vice e versa
*/
pred verificaRelacaoMedicosEPacientesCadastrados[]{
	all p1:Paciente, m1:Medico, t: Time | p1.statusPaciente.t = Cadastrado => p1 in m1.pacientes.t
	all p1:Paciente, m1:Medico, t: Time | p1.statusPaciente.t = NaoCadastrado => p1 !in m1.pacientes.t
	all m1:Medico, t: Time | m1.statusMedico.t = NaoCadastrado => #m1.pacientes = 0
}

/*
Todo gerente eh um medico cadastrado
*/
pred verificaGerenteCadastrado[]{
	all m1:Medico, s1:Servidor, t: Time | m1 in s1.gerentes  => m1.statusMedico.t = Cadastrado
}

/*
Indica que cada mÃ©dico tem no minÃ­mo 1 paciente e no mÃ¡ximo 3.
*/
pred cadaMedicoTemDe1a3Pacientes[]{
	all m1:Medico | #m1.pacientes < 4
}

/*
Todo paciente deve, obrigatoriamente, posssuir um sistema que irÃ¡ se comunicar com o Servidor.
*/
pred todoSistemaClienteEstaEmPaciente[]{
	all s:SistemaCliente, p:Paciente | s in p.sistemaPaciente
}

/*
Indica que o sistema tem dois gerentes, os quais sÃ£o mÃ©dicos tambÃ©m. Os gerentes sÃ£o imutÃ¡veis.
*/
pred oSistemaTem2GerentesDiferentes[]{
	all s1:Servidor | #s1.gerentes = 2
	all g1:Servidor.gerentes, g2: Servidor.gerentes - g1 | g1 != g2
}

/*
Este predicado indica que os logins de mÃ©dicos e pacientes devem ser diferentes.
*/
pred loginsDevemSerDiferentes[]{
	all p1:Paciente, p2:Paciente-p1 | p1.loginPaciente != p2.loginPaciente
	all m1:Medico, m2:Medico-m1 | m1.loginMedico != m2.loginMedico
	all m1:Medico, p1:Paciente| m1.loginMedico != p1.loginPaciente
}

/*
Impede que mÃ©dicos e pacientes tenham e-mails iguais.
*/
pred emailsDevemSerDiferentes[]{
	all p1:Paciente, p2:Paciente-p1 | p1.emailPaciente != p2.emailPaciente
	all m1:Medico, m2:Medico-m1 | m1.emailMedico != m2.emailMedico
	all m1:Medico, p1:Paciente| m1.emailMedico != p1.emailPaciente
}

/*
Os pacientes e medicos estao necessariamente no servidor.
*/
pred pacientesEMedicosDevemEstarNoServidor[]{
	all p1:Paciente |  p1 in pacientesNoServidor[Servidor]
	all m: Medico | m in medicosNoServidor[Servidor]
}

/*
Qualquer dado/informacao pertence a um mÃ©dico ou a um paciente.
*/
pred qualquerDadoPertenceAalguem[]{
	all n:Nome | n in todosOsNomes[Paciente, Medico]
	all l:Login | l in Paciente.loginPaciente + Medico.loginMedico
	all e:Email | e in Paciente.emailPaciente + Medico.emailMedico
	all s:Senha | s in Paciente.senhaPaciente + Medico.senhaMedico
	all d:DataDeNascimento | d in Paciente.data
}


/**2: Predicados que servem ao propÃ³sito de simular o comportamento temporal do sistema*/


pred init[t: Time]{}

pred acionaSuporte[t, t' : Time, su: Suporte ]{
	su.statusDoSuporte.t in SuporteNaoAcionado
	su.statusDoSuporte.t' = SuporteAcionado
}

pred cadastrarPaciente[t, t' : Time, p:Paciente, m:Medico ]{
	p.statusPaciente.t in NaoCadastrado
	p.statusPaciente.t' = Cadastrado
}

pred cadastrarMedico[t, t' : Time, m:Medico ]{
	m.statusMedico.t in NaoCadastrado
	m.statusMedico.t' = Cadastrado
}

pred alocaPaciente[t, t' : Time, p: Paciente, m: Medico]{
	p.statusPaciente.t in Cadastrado
	p not in Medico.pacientes.t
	m.pacientes.t' = m.pacientes.t + p
}

pred cadastrarSintoma[t,t' : Time, p: Paciente, si: Sintoma]{
	p.statusPaciente.t in Cadastrado
	si not in p.sintomas.t
	p.sintomas.t' = p.sintomas.t + si
}

pred show[]{}

/**FATOS*/

fact traces {
	init [first]
	all pre: Time - last | let pos = pre.next |
	some  p: Paciente, m: Medico, si: Sintoma, su: Suporte |
	cadastrarMedico[pre,pos,m] or
	acionaSuporte[pre, pos, su] or
	cadastrarPaciente[pre,pos,p,m] or 
	alocaPaciente[pre,pos,p, m] or 
	cadastrarSintoma[pre,pos,p, si]
	
}

fact EspecificacaoDoSistema{
	verificaRelacaoMedicosEPacientesCadastrados
	cadaMedicoTemDe1a3Pacientes
	oSistemaTem2GerentesDiferentes
	pacientesEMedicosDevemEstarNoServidor
	verificaGerenteCadastrado
	loginsDevemSerDiferentes
	emailsDevemSerDiferentes
	todoSistemaClienteEstaEmPaciente
	qualquerDadoPertenceAalguem	
}

/* Todos os pacientes dos medicos estao cadastrados */
fact fatosMedicos{
	all m: Medico, t: Time| m.pacientes.t.statusPaciente.t in Cadastrado
}

/* Todos os pacientes cadastrados no servidor, tem que ter o status cadastrado*/
fact fatosPaciente{
	all p: Paciente, sv: Servidor, t: Time | p in sv.pacientesCadastrados => p.statusPaciente.t in Cadastrado
}

/* Todos os sintomas devem pertecer a um paciente e cas o paciente nao seja cadastrado ele nao deve conter sintomas */
fact fatosSintomas{
	all p: Paciente, t: Time | p.statusPaciente.t in NaoCadastrado =>  #p.sintomas.t  = 0
	all si: Sintoma,  p: Paciente, t: Time | si in p.sintomas.t
}

/* Todos os status de cadastro devem pertencer a um paciente ou medico  */
fact fatosStatusCadastro{
	all p: Paciente, m : Medico, st: StatusCadastro, t : Time | st in p.statusPaciente.t or st in m.statusMedico.t
}


/* Todos os satus da internet devem pertencer a um sistema do paciente */
fact fatosStatusInternet{
	all s: SistemaCliente, st: StatusInternet | st in s.internet
	all st: StatusAcionado| st in SuporteAcionado or (st in SuporteNaoAcionado)
}

/****************************ASSERTS****************************/

/*
Todo medico atende de 1 a 3 pacientes apenas?
*/
assert medicosAtendemDe1a3pacientes{
	all m: Medico | #m.pacientes >= 1 and #m.pacientes <=3
}

/*
O sistema possui apenas 2 gerentes realmente?
*/
assert servidorPossuiApenas2Gerentes{
	all s: Servidor | #s.gerentes = 2
}

/*
Todo paciente cadastrado contÃÂ©m todos os seus dados de cadastro e nÃÂ£o os contÃÂ©m caso contrÃÂ¡rio?
*/
assert pacienteCadastradoContemTodosOsDados{
	all p: Paciente, t : Time |
	p.statusPaciente.t = Cadastrado
	implies
		#p.nomePaciente != 0 and
		#p.loginPaciente != 0 and
		#p.emailPaciente != 0 and
		#p.data != 0 and
		#p.senhaPaciente != 0 and
		#p.sistemaPaciente != 0 and
	
	all p: Paciente, t: Time |
	p.statusPaciente.t = NaoCadastrado
	implies
		#p.nomePaciente = 0 and
		#p.loginPaciente = 0 and
		#p.emailPaciente = 0 and
		#p.data = 0 and
		#p.senhaPaciente = 0 and
		#p.sistemaPaciente = 0 and
		#p.sintomas = 0
}

/*
Todo mÃÂ©dico cadastrado contÃÂ©m todos os seus dados de cadastro e nÃÂ£o os contÃÂ©m caso contrÃÂ¡rio?
*/
assert medicoCadastradoContemTodosOsDados{
	all m: Medico, t: Time | m.statusMedico.t = Cadastrado
		implies
			#m.nomeMedico != 0 and
			#m.loginMedico != 0 and
			#m.emailMedico != 0 and
			#m.senhaMedico != 0
	
	all m: Medico, t: Time | m.statusMedico.t = NaoCadastrado
		implies
			#m.nomeMedico = 0 and
			#m.loginMedico = 0 and
			#m.emailMedico = 0 and
			#m.senhaMedico = 0
}

/*
Todo dado possui um dono?
*/
assert todosOsDadosPossuemDono{
	all n: Nome, s: Senha, l: Login, d: DataDeNascimento, e: Email, p: Paciente, m: Medico | 
		(n in p.nomePaciente) or (n in m.nomeMedico) and
		(s in p.senhaPaciente) or (s in m.senhaMedico) and
		(l in p.loginPaciente) or (l in m.loginMedico) and
		(d in p.data) and
		(e in p.emailPaciente) or (e in m.emailMedico)
} 

/*
O sistema possui apenas um suporte?
*/
assert servidorPossuiApenas1Suporte{
	all s: Servidor | #s.suporte = 1
}

/*
A plataforma utilizada pelo sistema ÃÂ© Linux?
*/
assert plataformaDoServidorDeveSerLinux{
	all s: Servidor | s.plataformaServidor = Linux
}


run show for 10
