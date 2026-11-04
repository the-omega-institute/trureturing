using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class LieRadicalTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/LieRadicalTransfer.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Solvable extensions and actual radical quotients.", H("Lie radical transfer"),
        Blocks(
            Entry("solvable_of_solvable_kernel", "Solvable extensions",
                PairContext(All(X("f"), Hom(X("L"), X("M")),
                    Instance(Solvable(Ker), Instance(Solvable(X("M")), Solvable(X("L")))))),
                "For any Lie homomorphism over a field, a solvable kernel and a solvable codomain imply a solvable domain. The proof bounds the derived series of the domain first by the kernel and then by its own derived series. Surjectivity is not assumed.", DescribeRole.Theorem),
            Entry("kernel_eq_radical", "Identification of the actual radical",
                QuotientContext(Eq(Ker, Rad)),
                "For a Noetherian Lie algebra over a field, a surjective Lie map with solvable kernel and radical-free target has kernel equal to the actual solvable radical. The radical has solvable image under the surjection; that image must vanish. The reverse containment uses solvability of the kernel.", DescribeRole.Theorem),
            Entry("quotientEquiv_of_solvable_kernel", "An actual quotient equivalence",
                QuotientContext(Seq(X("quotientEquiv"), Sp, Colon, Sp,
                    Call("LieEquiv", X("k"), Call("Quotient", X("L"), Rad), X("M")))),
                "Under the same field, Lie algebra, Noetherian, surjectivity, solvable-kernel and trivial-target-radical hypotheses, the first isomorphism theorem gives an actual Lie equivalence from L modulo its actual radical to M. This conditional transfer lemma does not construct the required map for an evolution algebra.", DescribeRole.Definition),
            Entry("hasTrivialRadical_of_separating_surjections", "Separating radical-free quotients",
                SeparatingFormula(),
                "A family of surjective Lie maps to radical-free targets makes L radical-free when their kernels have zero intersection, stated by the exact separating law on each x. The index type can be infinite or empty; no finite dimensionality is required. Every abelian ideal has zero image in every target and therefore vanishes. These are classical Lie facts supporting the Ma-then-Zhang credited KMV application, not a priority claim or a completed evolution-algebra classification.", DescribeRole.Theorem))));
    private static Formula SeparatingFormula()
    {
        var index = X("aType");
        var a = X("a");
        var h = App(X("H"), a);
        Formula body = RadicalFree(X("L"));
        body = Imp(All(X("x"), X("L"),
            Imp(All(a, index, Eq(App(X("f"), a, X("x")), D(0))), Eq(X("x"), D(0)))), body);
        body = Imp(All(a, index, Call("Function.Surjective", App(X("f"), a))), body);
        body = All(X("f"), All(a, index, Hom(X("L"), h)), body);
        body = Instance(All(a, index, RadicalFree(h)), body);
        body = Instance(All(a, index, Call("LieAlgebra", X("k"), h)), body);
        body = Instance(All(a, index, Call("LieRing", h)), body);
        return LContext(All(index, Type, All(X("H"), new Formula.TypeArrow(index, Type), body)));
    }
    private static DocumentBlock.Describe Entry(string name, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula X(string s) => F.Id(s);
    private static Formula Type => Call("Type");
    private static Formula Qualified(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new Formula[] { Seq(Operatorname, Grp(X(part))) } :
            new Formula[] { Dot, Seq(Operatorname, Grp(X(part))) }).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Qualified(s), [.. xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Forall, Sp, Open, x, Sp, Colon, Sp, t, Close, Comma, Sp, Open, b, Close);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Hom(Formula l, Formula m) => Call("LieHom", X("k"), l, m);
    private static Formula Solvable(Formula l) => Call("LieAlgebra.IsSolvable", l);
    private static Formula RadicalFree(Formula l) => Call("LieAlgebra.HasTrivialRadical", X("k"), l);
    private static Formula Rad => Call("LieAlgebra.radical", X("k"), X("L"));
    private static Formula Ker => Call("LieHom.ker", X("f"));
    private static Formula LieContext(Formula l, Formula b) => All(l, Type,
        Instance(Call("LieRing", l), Instance(Call("LieAlgebra", X("k"), l), b)));
    private static Formula LContext(Formula b) => All(X("k"), Type,
        Instance(Call("Field", X("k")), LieContext(X("L"), b)));
    private static Formula PairContext(Formula b) => LContext(LieContext(X("M"), b));
    private static Formula QuotientContext(Formula b) => PairContext(
        Instance(Call("IsNoetherian", X("k"), X("L")), All(X("f"), Hom(X("L"), X("M")),
        Imp(Call("Function.Surjective", X("f")), Instance(Solvable(Ker), Instance(RadicalFree(X("M")), b))))));
}
