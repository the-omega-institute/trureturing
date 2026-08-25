using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class SymmetricBernoulliClosedFormsDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliClosedForms."
            + "symmetric_bernoulli_evidence_closed_forms";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four local evidence measures have exact closed forms on the symmetric two-point law pair.",
        H("Symmetric Bernoulli Evidence Closed Forms"),
        Blocks(Describe.Lean(
            DescribeId.Create("symmetric-bernoulli-evidence-closed-forms"),
            DeclarationHandle.Create(Declaration),
            H("Exact evidence of a symmetric two-point bias"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The positive-bias law assigns one half plus delta to true and one half "
                        + "minus delta to false; the negative-bias law swaps these masses.")),
                Paragraph(Text(
                    "Inside the open probability domain, direct two-coordinate evaluation "
                        + "gives total variation, affinity, squared Hellinger distance, and "
                        + "finite KL divergence simultaneously."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pow(Formula value, int exponent) =>
        Seq(value, Caret, Grp(D((byte)exponent)));

    private static Formula TheoremFormula()
    {
        Formula delta = DeltaLower;
        Formula bit = F.Id("b");
        Formula positiveLaw = new Formula.Subscript(F.Id("P"), delta);
        Formula negativeLaw = new Formula.Subscript(F.Id("Q"), delta);
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        Formula positiveMass = Call(
            "ite", bit,
            Seq(half, Sp, Plus, Sp, delta),
            Seq(half, Sp, Minus, Sp, delta));
        Formula negativeMass = Call(
            "ite", bit,
            Seq(half, Sp, Minus, Sp, delta),
            Seq(half, Sp, Plus, Sp, delta));
        Formula deltaAbs = Seq(Lvert, delta, Rvert);
        Formula deltaSquared = Pow(delta, 2);
        Formula radicand = Seq(D(1), Sp, Minus, Sp, D(4), Sp, deltaSquared);
        Formula root = Seq(Sqrt, Grp(radicand));
        Formula totalVariation = Call("TV", positiveLaw, negativeLaw);
        Formula affinity = Seq(Rho, Open, positiveLaw, Comma, Sp, negativeLaw, Close);
        Formula hellingerSquared = Pow(Call("H", positiveLaw, negativeLaw), 2);
        Formula divergence = Seq(
            F.Id("D"), Underscore, Grp(F.Id("KL")),
            Open, positiveLaw, Vert, Vert, Sp, negativeLaw, Close);
        Formula logRatio = Seq(
            Log, Open, Frac,
            Grp(D(1), Sp, Plus, Sp, D(2), Sp, delta),
            Grp(D(1), Sp, Minus, Sp, D(2), Sp, delta), Close);

        return Disp(Seq(
            Forall, Sp, bit, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Bool")), Comma,
            RowBreak, Grp(),
            Apply(positiveLaw, bit), Sp, Colon, Eq, Sp, positiveMass, Comma, Sp,
            Apply(negativeLaw, bit), Sp, Colon, Eq, Sp, negativeMass, Semi,
            RowBreak, Grp(),
            Forall, Sp, delta, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            deltaAbs, Sp, Lt, Sp, half, Sp, Rightarrow, RowBreak, Grp(),
            Open, totalVariation, Sp, Eq, Sp, D(2), Sp, deltaAbs, Close,
            Sp, Land, RowBreak, Grp(),
            Open, affinity, Sp, Eq, Sp, root, Close,
            Sp, Land, RowBreak, Grp(),
            Open, hellingerSquared, Sp, Eq, Sp,
            D(2), Open, D(1), Sp, Minus, Sp, root, Close, Close,
            Sp, Land, RowBreak, Grp(),
            Open, divergence, Sp, Eq, Sp,
            D(2), Sp, delta, Sp, logRatio, Close, Dot));
    }
}
