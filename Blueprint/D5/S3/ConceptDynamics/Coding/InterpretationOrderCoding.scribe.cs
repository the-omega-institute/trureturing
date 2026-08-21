using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class InterpretationOrderCodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Any chosen finite interpretation can receive the unique shortest prefix codeword.",
        H("Coding-Dependent Orders on Finite Interpretations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chosen-interpretation-receives-unique-shortest-codeword"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/InterpretationOrderCoding."
                        + "exists_prefix_code_with_chosen_unique_shortest"),
                H("Any chosen finite interpretation can be uniquely shortest"),
                StatementSource.FromAuthor(ChosenShortestFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite interpretation family is indexed by `Fin n`, and the chosen "
                            + "index itself witnesses that the family is nonempty. The code is "
                            + "injective and its range is prefix-free.")),
                    Paragraph(Text(
                        "The coding alphabet is `Bool x Fin n`, so it is allowed to depend on the "
                            + "interpretation family. The chosen interpretation receives a "
                            + "one-symbol word. Every other interpretation receives a two-symbol "
                            + "word whose first symbol separates it from the chosen word and whose "
                            + "second symbol records its index.")),
                    Paragraph(Text(
                        "Consequently, shortest code length cannot select an objective "
                            + "interpretation while the coding language is unconstrained: any "
                            + "designated interpretation can be made uniquely shortest. Restricting "
                            + "to acceptable universal languages and comparing only up to an "
                            + "invariance constant are boundary conditions motivated by this "
                            + "result; they are not formalized as additional conclusions here.")),
                    Paragraph(Text(
                        "Repository search found and directly reused `IsPrefixFree` from "
                            + "`D5/S0/Computability/Coding/PrefixFreeCode`. Pinned Mathlib provides "
                            + "the list prefix relation but no prefix-code predicate or theorem "
                            + "assigning a unique shortest codeword to a chosen labelled member. "
                            + "The repository Kraft converse is adjacent but returns an unlabelled "
                            + "list of codewords, so it does not prove this selected-member result."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PrefixFreeCode"))]));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ChosenShortestFormula()
    {
        Formula n = F.Id("n");
        Formula chosen = F.Id("i");
        Formula other = F.Id("j");
        Formula code = F.Id("c");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finN = Apply(Seq(Operatorname, Grp(F.Id("Fin"))), n);
        Formula alphabet = Seq(F.Id("Bool"), Sp, Times, Sp, finN);
        Formula words = Apply(Seq(Operatorname, Grp(F.Id("List"))), alphabet);
        Formula codeType = Seq(finN, Sp, To, Sp, words);
        Formula codeChosen = Apply(code, chosen);
        Formula codeOther = Apply(code, other);
        Formula chosenLength = Seq(Lvert, Sp, codeChosen, Sp, Rvert);
        Formula otherLength = Seq(Lvert, Sp, codeOther, Sp, Rvert);

        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            Forall, Sp, chosen, Colon, Sp, finN, Comma, Esc,
            Exists, Sp, code, Colon, Sp, codeType, Comma, Esc,
            Operatorname, Grp(F.Id("Injective")), Open, code, Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("IsPrefixFree")), Open,
            Operatorname, Grp(F.Id("range")), Open, code, Close, Close,
            Sp, Land, Esc,
            Forall, Sp, other, Colon, Sp, finN, Comma, Sp,
            other, Sp, Neq, Sp, chosen, Sp, Rightarrow, Sp,
            chosenLength, Sp, Lt, Sp, otherLength, Dot));
    }
}
