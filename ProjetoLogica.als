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
	plataformaServidor: one Linux
}

/*
Vão ser os clientes da nossa aplicação, eles vão ter um sistema cliente (em qualquer platarforma) que tenha acesso à internet
para poder se comunicar com o servidor. Além disso, eles podem estar ou não cadastrados no servidor.
*/
sig Paciente{
	data: one DataDeNascimento,
	nomePaciente: one Nome,
	sintomas: set Sintoma,
	emailPaciente: one Email,
	loginPaciente: one Login,
	senhaPaciente: one Senha,
	sistemaPaciente: one SistemaCliente,
	statusCliente:one StatusCadastro
}

/*
São os médicos que monitorarão os pacientes cadastrados. Cada médico poderá monitorar de 1 a 3 pacientes. O médico pode 
estar ou não cadastrado no servidor.
*/
sig Medico{
	pacientes: some Paciente,
	senhaMedico: one Senha,
	nomeMedico: one Nome,
	emailMedico: one Email,
	loginMedico: one Login,
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

abstract sig StatusCadastro{}

sig Cadastrado, NaoCadastrado extends StatusCadastro{}

abstract sig StatusInternet{}

sig ComInternet, SemInternet extends StatusInternet{}

sig SistemaOperacional{}

one	sig Linux extends SistemaOperacional{}

sig Senha{}

sig Login{}

sig Nome{}	

sig Email{}

sig DataDeNascimento{}

sig Sintoma{}

/**FUNÇÕES UTILITÁRIAS USADAS EM VÁRIAS SEÇÕES DO CÓDIGO*/

fun pacientesCadastradosComMedico[m: Medico]: set Paciente{
	m.pacientes
}


fun pacienteCadastradosNoServidor[s: Servidor]: set Paciente{
	s.pacientes.statusCliente
}


fun medicosCadastradosNoServidor[s: Servidor]: set Medico{
	s.medicos
}

/**PREDICADOS*/

pred loginPacientesDeveSerDiferente[]{
	all p1:Paciente, p2:Paciente-p1 | p1.loginPaciente != p2.loginPaciente
}

pred emailPacientesDeveSerDiferente[]{
	all p1:Paciente, p2:Paciente-p1 | p1.emailPaciente != p2.emailPaciente
}

pred loginMedicosDeveSerDiferente[]{
	all m1:Medico, m2:Medico-m1 | m1.loginMedico != m2.loginMedico
}

pred emailMedicosDeveSerDiferente[]{
	all m1:Medico, m2:Medico-m1 | m1.emailMedico != m2.emailMedico
}

pred pacienteAutenticado[l: Login, s: Senha]{
	all p:Paciente | p in Servidor.pacientes and
   	p.loginPaciente = l and p.senhaPaciente = s
}

pred acionarSuporte[]{}

pred cadastrarGerente[]{}

pred cadastrarSintoma[]{}


pred show[]{}

/**FATOS*/

fact fatosPaciente{
	loginPacientesDeveSerDiferente
	emailPacientesDeveSerDiferente
	all p1:Paciente |  p1 in Servidor.pacientes
	
}

fact fatosMedico{
	all m1:Medico | #m1.pacientes < 3
	loginMedicosDeveSerDiferente
	emailMedicosDeveSerDiferente
	all m: Medico | m in Servidor.medicos
}

fact fatosSistemaCliente{
	all s:SistemaCliente, p:Paciente | s in p.sistemaPaciente
}

fact fatosSistemaServidor{
    #Servidor = 1
	all s1:Servidor | #s1.gerentes = 2
	all g1:Servidor.gerentes, g2: Servidor.gerentes - g1 | g1 != g2
	all m1:Medico, p1:Paciente| m1.emailMedico != p1.emailPaciente
	all m1:Medico, p1:Paciente| m1.loginMedico != p1.loginPaciente
}


fact fatosNome{
	all n:Nome | n in Paciente.nomePaciente + Medico.nomeMedico
}

fact fatosStatusInternet{
	all s: SistemaCliente, t: StatusInternet | t in s.internet
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

run show for 5
