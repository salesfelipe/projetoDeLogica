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

-- Plataforma tem que ser linux
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
Servidor é onde vai ficar contido os dados da aplicação, respondendo a requisição dos sistemas
dos pacientes cadastrados. Este servidor tem que rodar em Linux.
*/
one sig Servidor{
	gerente: some Medico,
	medicoCadastrado: Medico some  -> Time,
	pacienteCadastrado: set Paciente,
	sistemaAplicacao: one Linux
}

/*
Vão ser os clientes da nossa aplicação, eles vão ter um sistema que tem quer ser conectado a internet
para poder se comunicar com o servidor.
*/
sig Paciente{
	data: one DataDeNascimento,
	nomePaciente: one Nome,
	sintomas: set Sintoma,
	emailPaciente: one Email,
	loginPaciente: one Login,
	senhaPaciente: one Senha,
	sistemaPaciente: one Sistema
}

/*
Além de tratar dos pacientes, três mais precisamente, dois deles vão ficar responsáveis por cadastrar 
mais médicos ao sistema e chamar o suporte se necessário.
*/
sig Medico{
	pacientes: some Paciente,
	senhaMedico: one Senha,
	nomeMedico: one Nome,
	emailMedico: one Email,
	loginMedico: one Login
}

sig Sistema{
	Internet: StatusInternet -> Time
}

abstract sig StatusInternet{}

one sig ComAcesso, SemAcesso extends StatusInternet{}

sig SistemaOperacional{}

one 	sig Linux extends SistemaOperacional{}

sig Senha{}

sig Login{}

sig Nome{}	

sig Email{}

sig DataDeNascimento{}

sig Sintoma{}

/**FUNÇÕES UTILITÁRIAS USADAS EM VÁRIAS SEÇÕES DO CÓDIGO*/

/**FATOS*/


fact fatosPaciente{
	all p1:Paciente, p2:Paciente-p1 | p1.emailPaciente != p2.emailPaciente
	all p1:Paciente, p2:Paciente-p1 | p1.loginPaciente != p2.loginPaciente
	all p1:Paciente |  p1 in Servidor.pacienteCadastrado
	all p1:Paciente | p1 in Medico.pacientes
}

fact fatosMedico{
	all m1:Medico | #m1.pacientes < 3
	all m1:Medico, m2:Medico-m1 | m1.loginMedico != m2.loginMedico
	all m1:Medico, m2:Medico-m1 | m1.emailMedico != m2.emailMedico
}

fact fatosSistemaCliente{
	all s:Sistema, p:Paciente | s in p.sistemaPaciente
}

fact fatosSistemaServidor{
    #Servidor = 1
	all s1:Servidor | #s1.gerente = 2
	all g1:Medico | g1 in Medico
	all g1:Medico, g2: Medico - g1 | g1 != g2
	all m1:Medico, p1:Paciente| m1.emailMedico != p1.emailPaciente
	all m1:Medico, p1:Paciente| m1.loginMedico != p1.loginPaciente
}


fact fatosNome{
	--Todo nome está vinculado a um aluno
	all n:Nome | n in Paciente.nomePaciente + Medico.nomeMedico
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

/**PREDICADOS*/


pred pacienteAutenticado[l: Login, s: Senha]{
	all p:Paciente | p in Servidor.pacienteCadastrado and
   	p.loginPaciente = l and p.senhaPaciente = s
}

/*
pred adicionaPacienteNoCadastro[p:Paciente, g:Gerente, s : SistemaDeAssistenciaHospitalar, t,t': Time]{

}

pred removePacienteNoCadastro[p:Paciente, g:Gerente, s : SistemaDeAssistenciaHospitalar, t,t': Time]{

}
*/

pred adicionarMedico[m: Medico, t, t': Time]{
	m not in Servidor.~(medicoCadastrado.t)
	Servidor.~(medicoCadastrado.t') = ~(Servidor.medicoCadastrado.t) + m
}
pred acionarSuporte[]{}
pred cadastrarGerente[]{}
pred cadastrarPaciente[p: Paciente, l: Login, s: Senha]{}
pred cadastrarSintoma[]{}


pred show[]{}

run show for 5
