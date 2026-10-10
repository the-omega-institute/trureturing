using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class Sl2WeightInjectivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lowering powers are injective at natural weights under local raising nilpotence.",
        H("Weight injectivity for an sl₂ triple"),
        Blocks(Describe.Lean(
            DescribeId.Create("sl-two-lowering-kernel-zero"),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/Sl2WeightInjectivity.lowering_kernel_zero"),
            H("Zero kernel of a lowering power"),
            StatementSource.FromAuthor(KernelFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "This standard fact about sl₂ triples generalizes the rational lemma used by HypereclecticNonShortening. The operators h, e and f are respectively the weight, raising and lowering operators. If v has natural weight q, a raising power annihilates v, and k is at most q, then f to the kth power can annihilate v only when v is zero. Induction on the raising exponent reduces to a primitive vector, whose lowering chain is nonzero through its highest weight. The field has characteristic zero; neither finite dimensionality nor global nilpotence is assumed. Powers of endomorphisms use composition, and the dot denotes scalar multiplication."))),
            DescribeRole.Theorem)),
        []));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Assumption(Formula value, Formula body) =>
        Seq(OpenBracket, value, CloseBracket, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula ImpliesThat(Formula premise, Formula body) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, body);

    private static Formula KernelFormula()
    {
        var field = F.Id("K"); var space = F.Id("V");
        var h = F.Id("h"); var e = F.Id("e"); var f = F.Id("f");
        var n = F.Id("n"); var v = F.Id("v"); var q = F.Id("q"); var k = F.Id("k");
        var nats = Seq(Mathbb, Grp(F.Id("N")));
        var end = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("Module"), Dot, F.Id("End"))), [field, space]);
        var weight = Equal(At(h, v), Seq(Par(Seq(q, Sp, Colon, Sp, field)), Sp, Cdot, Sp, v));
        var bound = new Formula.Relation(k, FormulaRelationOperator.LessThanOrEqual, q);
        var raising = Equal(At(Par(new Formula.Power(e, n)), v), D(0));
        var lowering = Equal(At(Par(new Formula.Power(f, k)), v), D(0));
        Formula body = ImpliesThat(weight, ImpliesThat(bound, ImpliesThat(raising,
            ImpliesThat(lowering, Equal(v, D(0))))));
        body = All("k", nats, body);
        body = All("q", nats, body);
        body = All("v", space, body);
        body = All("n", nats, body);
        body = Assumption(new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("IsSl"), D(2), F.Id("Triple"))), [h, e, f]), body);
        body = All("f", end, body);
        body = All("e", end, body);
        body = All("h", end, body);
        body = Assumption(Call("Module", field, space), body);
        body = Assumption(Call("AddCommGroup", space), body);
        body = All("V", Call("Type"), body);
        body = Assumption(Call("CharZero", field), body);
        body = Assumption(Call("Field", field), body);
        return Disp(All("K", Call("Type"), body));
    }
}
