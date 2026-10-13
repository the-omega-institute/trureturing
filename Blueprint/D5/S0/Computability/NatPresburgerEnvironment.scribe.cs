using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class NatPresburgerEnvironmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversed bound coordinates align native snoc with the backend binder head.", H("Native coordinates in integer valuations"),
        Blocks(Paragraph(Text("For arbitrary natural m and n, v:Fin m->Nat is the free valuation and xs:Fin n->Nat is the bound valuation. NatTuple(r) abbreviates Fin r->Nat. environment(v,xs) is reverse(List.ofFn(cast o xs)) followed by List.ofFn(cast o v). Thus a free coordinate i lies at n+i and a bound coordinate i lies at n-1-i. The sum type distinguishes them even if the numerical indices coincide.")),
            Paragraph(Text("basis(k) is an affine expression with coefficient one at k, zero elsewhere and constant zero. It is built recursively with consCoeff; missing valuation entries contribute zero. Native coordinates are proved present by environment_lookup. For m=0 or n=0 the corresponding domain is empty, and when both vanish the environment is the empty list.")),
            Describe.Lean(DescribeId.Create("eval-basis"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerEnvironment.eval_basis"),
            H("The affine coordinate reads its list entry"), StatementSource.FromAuthor(F.Disp(A("k", V("Nat"), A("env", Call("List", V("Int")), E(Call("eval",Call("basis",V("k")),V("env")),Call("getD",Call("getOptional",V("env"),V("k")),Num(0))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Induction on k, generalized over the list, removes one affine coefficient and one list head together. The nil branch proves the same zero-default convention at every index."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("environment-lookup"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerEnvironment.environment_lookup"),
            H("Native sum coordinates are exact"), StatementSource.FromAuthor(F.Disp(A("m",V("Nat"),A("n",V("Nat"),A("v",Call("NatTuple",V("m")),A("xs",Call("NatTuple",V("n")),A("i",Call("Sum",Call("Fin",V("m")),Call("Fin",V("n"))),E(Call("getD",Call("getOptional",Call("environment",V("v"),V("xs")),Call("position",V("i"))),Num(0)),Call("cast",Call("elim",V("v"),V("xs"),V("i"))))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("The free branch uses lookup in the right part of an appended list. The bound branch uses lookup in the left part and the reversal index identity. No positive-context assumption is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("environment-snoc"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerEnvironment.environment_snoc"),
            H("Appending a native bound value creates the integer head"), StatementSource.FromAuthor(F.Disp(A("m",V("Nat"),A("n",V("Nat"),A("v",Call("NatTuple",V("m")),A("xs",Call("NatTuple",V("n")),A("x",V("Nat"),E(Call("environment",V("v"),Call("snoc",V("xs"),V("x"))),Call("cons",Call("cast",V("x")),Call("environment",V("v"),V("xs"))))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("The supplied List.ofFn snoc identity, followed by reversal and append normalization, gives this list equality. It aligns the native universal binder with the integer de Bruijn convention."))), DescribeRole.Theorem)), [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/PresburgerSyntax"))]));

    private static Formula V(string name) => F.Id(name);
    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula E(Formula left, Formula right) => F.Seq(left, F.Sp, F.Eq, F.Sp, right);
}
