using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyOddRowsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/HeadleyOddRows.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gordon predecessor connects every row without treating an odd abelian group as cyclic.", H("HeadleyOddRows"), Blocks(
            Describe.Lean(
                DescribeId.Create("headleyoddrows-predecessor-orbit"),
                DeclarationHandle.Create(Owner + "predecessor_orbit"), H("Positive wrap and the complete predecessor orbit"),
                StatementSource.FromAuthor(Disp(Orbit())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For N=volume(ds)>0, the i-th predecessor of zero is residue(N-i) for every i up to N, closure included. The proof invokes the original positive-index pred_residue at N-i; it never applies that theorem at zero. The empty radix list has N=1 and remains in scope. Rank is a set equivalence, not an additive group coordinate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddrows-predecessor-cycle"),
                DeclarationHandle.Create(Owner + "predecessor_cycle"), H("One cycle on every mixed-radix row"),
                StatementSource.FromAuthor(Disp(Cycle())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual predecessor equivalence has inverse x↦residue(rank(x)+1). Positive-index predecessor steps take every residue to zero, so every row is on the same cycle. The original GordonCarry rankEquiv, rank_residue, residue_zero and pred_residue are reused directly; GordonProduct residue_eq_iff is exposed at its original owner without changing its proof."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddrows-delta-zero-spec"),
                DeclarationHandle.Create(Owner + "delta_zero_spec"), H("The ordinary row difference"),
                StatementSource.FromAuthor(Disp(Delta(false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The row map is negation. Its actual difference is negative doubling, which is a permutation by the original box_two_injective and finiteness. The inverse is negative half, where half is the inverse of that original doubling map."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddrows-delta-one-spec"),
                DeclarationHandle.Create(Owner + "delta_one_spec"), H("The carry supplies the distinguished actual difference"),
                StatementSource.FromAuthor(Disp(Delta(true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The distinguished row map is pred after negation. Its coefficient-one difference is -carry(-h)-ones, with the sign derived from the original carry definition. Both maps are actual equivalences: their inverses are negative successor and negative inverse-carry evaluated at -y-ones. No row orthomorphism is assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddrows-row-return"),
                DeclarationHandle.Create(Owner + "row_return"), H("Traversal order gives predecessor"),
                StatementSource.FromAuthor(Disp(Return())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying negation and then the distinguished row map gives pred. This equality is the row return used by HeadleyOddProduct. It replaces the cyclic translation used by the earlier native inverse-pair construction and works for noncyclic odd groups."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddrows-odd-box"),
                DeclarationHandle.Create(Owner + "odd_box"), H("A consumed normalization of the original unconditional decomposition"),
                StatementSource.FromAuthor(Disp(OddBox())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original GordonFullSet finite_abelian_presentation, chain_classification and case_transport supply the unconditional trichotomy. Odd cardinality excludes the two even alternatives, using the original card_even_of_power_box. Their original statements, assumptions and proof bodies are preserved; only listed visibility changes are made. This is not a new decomposition theorem and does not invoke the nonzero-total sequencing result. The full product registration attempt and its remaining dependent-family obligations are disclosed at https://github.com/the-omega-institute/trureturing/issues/21042; the existing successful GordonCarry registration is preserved."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Digits(Formula body) => All("ds", Call("List", F.Id("OddRadix")), body);
    private static Formula Box() => Call("Box", F.Id("ds"));
    private static Formula Row(string name, Formula h) => Call(name, F.Id("ds"), h);
    private static Formula Instance(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Orbit() => Digits(All("i", F.Id("Nat"),
        Imp(Le(F.Id("i"), Call("volume", F.Id("ds"))),
            Eq(Call("apply", Call("pow", Call("predecessor", F.Id("ds")), F.Id("i")), D(0)),
                Call("residue", F.Id("ds"), Sub(Call("volume", F.Id("ds")), F.Id("i")))))));
    private static Formula Cycle() => Digits(Call("IsCycleOn", Call("predecessor", F.Id("ds")), Call("univ", Box())));
    private static Formula Delta(bool one) => Digits(All("h", Box(),
        Eq(Row(one ? "deltaOne" : "deltaZero", F.Id("h")),
            Sub(Row(one ? "rowOne" : "rowZero", F.Id("h")), F.Id("h")))));
    private static Formula Return() => Digits(All("h", Box(),
        Eq(Row("rowOne", Row("rowZero", F.Id("h"))), Row("predecessor", F.Id("h")))));
    private static Formula OddBox() => All("H", F.Id("Type"),
        Seq(Instance("AddCommGroup", F.Id("H")), Instance("Fintype", F.Id("H")),
            Imp(Call("Odd", Call("card", F.Id("H"))),
                Ex("ds", Call("List", F.Id("OddRadix")),
                    Call("Nonempty", Call("AddEquiv", F.Id("H"), Box()))))));
}
