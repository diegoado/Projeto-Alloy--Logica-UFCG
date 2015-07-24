module SistemaDePermissao

	sig Diretorio{
		diretoriospais: lone Diretorio,
		arquivos: set Arquivo
}{
		this !in this.^@diretoriospais
		this != Root => Root in this.^@diretoriospais
}

	sig Arquivo{
}

	one sig Root extends Diretorio {}{ no this.@diretoriospais}

	pred show[]{}
	run show for 3
