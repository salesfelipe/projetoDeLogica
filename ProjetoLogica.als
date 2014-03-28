module banco

sig Paciente{
	data: one DataDeNascimento,
	nome: one Nome,	
	sintomas: set Sintoma,
	email: one Email,
	usuario: one Nome,
	senha: one Senha
}

sig Medico{
	pacientes: set Paciente	

}

sig Senha{}

sig Nome{}	

sig Email{}

sig DataDeNascimento{}

sig Sintoma{}

sig Sistema{}

fact fatosPaciente{
	all p1:Paciente, p2:Paciente-p1 | p1.nome != p2.nome
	all p1:Paciente, p2:Paciente-p1 | p1.senha != p2.senha	
}


-- Plataforma tem que ser linux, predicado para verificar isso, tem que ter uma assinatura de sistema
-- O sistema vai ter uma linha com o paciente e vai ter que checar se o paciente tem acesso ao servidor
-- O gerente vai ser um medico, e sao imutaveis

fact fatosNome{
	--Todo nome está vinculada a um aluno
	all n:Nome | n in Paciente.nome
}

pred show[]{}



run show for 5
