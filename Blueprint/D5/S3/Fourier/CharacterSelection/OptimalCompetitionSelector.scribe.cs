using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class OptimalCompetitionSelectorDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive projection margin produces the normalized selector that removes every competitor.",
        H("Optimal Competition Selector"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("character-profile-space"),
                DeclarationHandle.Create(Prefix + "CharacterProfileSpace"),
                H("Finite complex character-profile space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient carrier is EuclideanSpace C (Fin d), the finite complex "
                        + "coordinate space named in the source chain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-dot"),
                DeclarationHandle.Create(Prefix + "profileDot"),
                H("Underlying real profile pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Because the competitor span is real, the source dot product is represented "
                        + "by the underlying real inner product on the complex coordinate space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("competitor-profile-space"),
                DeclarationHandle.Create(Prefix + "competitorProfileSpace"),
                H("Real span of competitor profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "W is the real submodule spanned by the finite family Phi(z_j)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("selector-margin"),
                DeclarationHandle.Create(Prefix + "selectorMargin"),
                H("Target-to-competitor margin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Delta is the metric distance from the target profile to the real competitor "
                        + "span."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimal-competition-selector"),
                DeclarationHandle.Create(Prefix + "optimal_competition_selector"),
                H("The normalized complementary projection is optimal"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the sole substantive premise Delta > 0, the displayed witness has "
                            + "unit norm and belongs to the orthogonal complement of W.")),
                    Paragraph(Text(
                        "The same public result states all three displayed source conclusions: "
                            + "every competing profile is annihilated, the absolute target response "
                            + "is Delta, and the witness equals the normalized complementary "
                            + "projection."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula dimension = F.Id("d");
        Formula competitorCount = F.Id("m");
        Formula profile = F.Id("Phi");
        Formula target = new Formula.Subscript(F.Id("z"), D(0));
        Formula competitors = F.Id("z");
        Formula index = F.Id("j");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula profileSpace = Call("EuclideanSpace", complex, Call("Fin", dimension));
        Formula profileFamily = Seq(complex, Sp, To, Sp, profileSpace);
        Formula competitorFamily = Seq(Call("Fin", competitorCount), Sp, To, Sp, complex);
        Formula targetProfile = Apply(profile, target);
        Formula competitorProfile = Apply(profile, Apply(competitors, index));
        Formula space = F.Id("W");
        Formula orthogonal = Seq(space, Caret, Grp(Perp));
        Formula delta = F.Id("Delta");
        Formula selector = new Formula.Subscript(F.Id("c"), Star);
        Formula projection = Call("starProjection", orthogonal, targetProfile);
        Formula selectorFormula = Equal(
            selector,
            Seq(Call("norm", projection), Caret, Grp(Minus, D(1)), Sp, Cdot, Sp, projection));
        Formula competitorClause = Seq(
            Forall, Sp, index, Colon, Sp, Call("Fin", competitorCount), Comma, Sp,
            Equal(Call("profileDot", selector, competitorProfile), D(0)));
        Formula targetClause = Equal(
            Call("abs", Call("profileDot", selector, targetProfile)), delta);
        Formula witnessClauses = And(
            Equal(Call("norm", selector), D(1)),
            And(
                Seq(selector, Sp, InMacro, Sp, orthogonal),
                And(Grp(competitorClause), And(targetClause, selectorFormula))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, dimension, Comma, Sp, competitorCount, Colon, Sp,
            Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            profile, Colon, Sp, profileFamily, Comma, Sp,
            target, Colon, Sp, complex, Comma, Sp,
            competitors, Colon, Sp, competitorFamily, Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            space, Sp, Colon, Eq, Sp, Call("competitorProfileSpace", profile, competitors),
            Comma, Sp, delta, Sp, Colon, Eq, Sp,
            Call("selectorMargin", profile, target, competitors), Close, SemiSpace, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, delta, Sp, Rightarrow, Sp,
            Exists, Sp, selector, Colon, Sp, profileSpace, Comma, Sp,
            witnessClauses, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
