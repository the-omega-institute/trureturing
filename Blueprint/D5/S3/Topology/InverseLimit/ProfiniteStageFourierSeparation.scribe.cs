using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class ProfiniteStageFourierSeparationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.";

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Stage(Formula m, Formula x) => Call("coordinate", m, x);

    private static Formula Correlation(Formula m, Formula x, Formula y) =>
        Call("finiteCorrelation", m, x, y);

    private static Formula Statement()
    {
        Formula nat = F.Id("Nat");
        Formula pi = F.Id("ProfiniteIntegers");
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula character = Call("coordinateCharacter", m, k, x);
        Formula characterY = Call("coordinateCharacter", m, k, y);
        Formula finiteCorrelation = Call("finiteCorrelation", m, x, y);
        Formula equality = Eq(x, y);
        Formula allNonzero = All("m", nat, Ne(Correlation(F.Id("m"), x, y), Call("zero")));

        Formula continuity = All("m", nat,
            All("k", Call("ZMod", Call("succ", F.Id("m"))),
                All("x", pi, Call("ContinuousAddChar", character))));
        Formula correlation = All("m", nat,
            Eq(finiteCorrelation,
                Call("if", Eq(Stage(m, x), Stage(m, y)),
                    Call("card", Call("ZMod", Call("succ", m))), Call("zero"))));
        Formula separation = Imp(Ne(x, y), Exists("m", nat,
            Exists("k", Call("ZMod", Call("succ", F.Id("m"))),
                Ne(Call("coordinateCharacter", F.Id("m"), F.Id("k"), x),
                    Call("coordinateCharacter", F.Id("m"), F.Id("k"), y)))));

        return Disp(And(continuity, And(correlation, And(Iff(equality, allNonzero), separation))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additive characters separate compatible profinite residue families.",
        H("Finite-stage Fourier separation of profinite integers"),
        Blocks(
            Paragraph(Text(
                "ProfiniteIntegers is the compatible family of residues in ZMod (m+1) for all natural stages m. "
                + "At each stage, coordinateCharacter m k is the additive character x ↦ toAddCircle(k · x(m)); it is continuous because each finite residue space is discrete and coordinate evaluation is continuous. "
                + "The use of m+1 indexes all positive finite moduli, including ZMod 1 at m=0. "
                + "The displayed sum is over the complete finite residue group and uses the standard primitive additive character.")),
            Describe.Lean(
                DescribeId.Create("coordinate-character"),
                DeclarationHandle.Create(Owner + "coordinateCharacter"),
                H("Continuous finite-stage character"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "coordinateCharacter packages one finite residue character as a continuous additive homomorphism from the profinite inverse-limit space to UnitAddCircle. "
                    + "The proof supplies the additive laws through ZMod.toAddCircle and continuity through the discrete finite coordinate followed by the product-coordinate projection."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stage-correlation"),
                DeclarationHandle.Create(Owner + "stage_correlation"),
                H("Complete finite Fourier correlation"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a fixed stage m, the complete standard-character sum of the difference x(m)-y(m) is the cardinality m+1 when the two residues agree and is zero otherwise. "
                    + "This is Mathlib's AddChar.sum_mulShift specialized to ZMod (m+1) and its primitive standard character."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profinite-fourier-separates"),
                DeclarationHandle.Create(Owner + "profinite_fourier_separates"),
                H("A separating stage has zero correlation"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If two compatible residue families differ, their underlying functions differ at some finite natural stage. "
                    + "The stage-correlation formula then gives a zero complete Fourier correlation at that stage."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profinite-fourier-reflects"),
                DeclarationHandle.Create(Owner + "profinite_fourier_reflects"),
                H("All-stage nonzero correlations reflect equality"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality implies every stage difference is zero, so every complete correlation is the nonzero cardinality m+1. "
                    + "Conversely, a distinct pair has the zero correlation supplied by profinite_fourier_separates, contradicting the all-stage nonzero hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continuous-character-separates"),
                DeclarationHandle.Create(Owner + "continuous_character_separates"),
                H("Continuous characters separate points"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A differing finite coordinate is detected already by the coefficient k=1 character. "
                    + "Injectivity of ZMod.toAddCircle turns equality of the character values into equality of the finite residues, yielding a contradiction."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/ProfiniteIntegers"))]));
}
