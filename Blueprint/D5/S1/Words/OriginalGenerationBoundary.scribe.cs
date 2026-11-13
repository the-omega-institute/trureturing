using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class OriginalGenerationBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third Fibonacci substitution iterate is conjugate to the two block images through 01.",
        H("Original Generation Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tau-morphism"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.tau"),
                H("The two block images"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With false representing 0 and true representing 1, tau maps 0 to "
                        + "B5 = 00101 and 1 to B3 = 001."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-fibonacci-iterate"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.sigmaThree"),
                H("The third iterate in the source alphabet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical GoldenGapWord.subst maps true to [true, false] and false "
                        + "to [true]. Complementing input and output letters gives sigma(0) = 01 "
                        + "and sigma(1) = 0. sigmaThree complements the input word, applies "
                        + "FibonacciIncidence.iterate three times, and complements the result. "
                        + "Since Bool complement is an involution, this is the third iterate of sigma."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tau-word"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.tauWord"),
                H("Concatenating the block images"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "tauWord concatenates tau's images in the order of an arbitrary finite Bool word."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boundary-conjugacy"),
                DeclarationHandle.Create(
                    "D5/S1/Words/OriginalGenerationBoundary.original_generation_boundary"),
                H("Abstract finite-word boundary conjugacy"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite word w, sigmaThree(w) followed by 01 equals 01 followed "
                        + "by tauWord(w). The two letter identities extend by induction over w: "
                        + "the boundary moves past each substituted letter. This is the abstract "
                        + "conjugacy clause of Proposition 51.2 of Atomic Generation and Acquisition IV. "
                        + "It does not identify w with return types acquired from the specified source, "
                        + "locate source markers or a cursor, or establish the actual prefix equation "
                        + "W_m = U_K tau(w) 00. Those claims require a source and acquisition bridge. "
                        + "The displayed conjugating word is 01; the acquisition marker 00 has a "
                        + "different role. No bracketed tree or edit history is reconstructed."))),
                DescribeRole.Theorem)),
        []));

    private static Formula BoundaryFormula()
    {
        var w = F.Id("w");
        var boolList = Seq(Operatorname, Grp(F.Id("List")), Sp, Operatorname, Grp(F.Id("Bool")));
        var zeroOne = Seq(OpenBracket, F.Id("false"), Comma, Sp, F.Id("true"), CloseBracket);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("w"),
            boolList, new Formula.Relation(
                Append(Call("sigmaThree", w), zeroOne), FormulaRelationOperator.Equal,
                Append(zeroOne, Call("tauWord", w)))));
    }

    private static Formula Append(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Plus, Plus, Sp, Open, right, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
