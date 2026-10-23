using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class NatPresburgerCompilerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every native binder receives its own nonnegative integer guard.", H("A structural Nat-to-Int semantic compiler"),
        Blocks(Paragraph(Text("BF(m,n) abbreviates presburger.BoundedFormula (Fin m) n, and NatTerm(m,n) abbreviates presburger.Term (Fin m sum Fin n). Bounded refers to the finite variable context, not to a numerical bound on the quantified values. All m,n, including zero, all natural valuations and every finite formula are in scope.")),
            Paragraph(Text("compileTerm maps variables to basis(position i), zero and one to integer affine constants, and addition to affine addition. The native language has no relation symbols: the relation branch eliminates the Empty relation type, with no fallback. Term induction connects affine evaluation to the integer cast of the original native Term.realize.")),
            Paragraph(Text("compile maps falsum to false; equality s=t to the conjunction 0<=s-t and 0<=-(s-t); implication to not-left or right. Each native all body becomes the backend all of the implication from 0<=head to compile(body). The child is compiled in its own larger native context; it is not shifted a second time.")),
            Paragraph(Text("The nonnegative guard is added at every binder, including binders occurring under negation and in arbitrarily alternating formulas. A guard only at the outermost binder would change Nat semantics. Native existential and negation constructions already use implication and all, so the same structural proof covers them. No bound on numeral size, context size or quantifier nesting is assumed.")),
            Describe.Lean(DescribeId.Create("compile-term-correct"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerCompiler.compile_term_correct"),
            H("Exact native term values"), StatementSource.FromAuthor(F.Disp(A("m",V("Nat"),A("n",V("Nat"),A("t",Call("NatTerm",V("m"),V("n")),A("v",Call("NatTuple",V("m")),A("xs",Call("NatTuple",V("n")),E(Call("eval",Call("compileTerm",V("t")),Call("environment",V("v"),V("xs"))),Call("cast",Call("realizeTerm",V("t"),Call("elim",V("v"),V("xs")))))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("The variable case composes eval_basis with environment_lookup. Zero, one and addition use the native function interpretation and upstream affine evaluation laws. This is a native structural semantic bridge; it does not reprove Cooper elimination."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("compile-correct"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerCompiler.compile_correct"),
            H("Exact native formula semantics"), StatementSource.FromAuthor(F.Disp(B(A("xs", Call("NatTuple", V("n")), I(Call("holds", Call("compile", V("p")), Call("environment", V("v"), V("xs"))), Call("Realize", V("p"), V("v"), V("xs"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Formula induction treats equality by term preservation and injectivity of the Nat cast. At all, environment_snoc aligns the new coordinate. A natural x supplies a nonnegative integer cast; conversely a guarded integer z supplies z.toNat with cast(z.toNat)=z. This proves both quantified directions, and induction preserves every implication, negation and alternation."))), DescribeRole.Theorem)), [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/NatPresburgerEnvironment"))]));

    private static Formula V(string name) => F.Id(name);
    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula E(Formula left, Formula right) => F.Seq(left, F.Sp, F.Eq, F.Sp, right);
    private static Formula I(Formula left, Formula right) => F.Seq(F.Open, left, F.Close, F.Sp, F.Iff, F.Sp, F.Open, right, F.Close);
    private static Formula U(Formula body) => A("m", V("Nat"), A("n", V("Nat"),
        A("p", Call("BF", V("m"), V("n")), body)));
    private static Formula B(Formula body) => U(A("v", Call("NatTuple", V("m")), body));
}
