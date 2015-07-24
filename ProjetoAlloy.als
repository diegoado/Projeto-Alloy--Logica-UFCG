module SistemaDePermissao

	sig Diretorio{
		diretoriopai: lone Diretorio,
		arquivos: set Arquivo
}
	fact {
		all d: Diretorio | d !in d.^diretoriopai
		all d: Diretorio | (d != Root) => (Root in d.^diretoriopai)
		no Root.diretoriopai
}

	sig Arquivo{
}

	one sig Root extends Diretorio {}

	pred show[]{}
	run show for 3
