using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class ErrorErasureUniqueDecodingDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Coding/ErrorErasureUniqueDecoding.error_erasure_unique_decoding";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A code of minimum distance d has a unique legal message whenever twice the "
            + "unknown-error budget plus the known-erasure budget is below d.",
        H("Joint Error-and-Erasure Unique Decoding"),
        Blocks(Describe.Lean(
            DescribeId.Create("joint-error-and-erasure-condition-gives-unique-decoding"),
            DeclarationHandle.Create(Declaration),
            H("The joint error-and-erasure condition gives unique decoding"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix the known erased-coordinate finset E. A legal candidate is "
                        + "compatible with the received word when it disagrees on at most e "
                        + "coordinates outside E.")),
                Paragraph(Text(
                    "Any coordinate where two compatible candidates disagree lies either in "
                        + "E, in the first candidate's unerased error set, or in the second "
                        + "candidate's unerased error set. Their Hamming distance is therefore "
                        + "at most s + e + e. The strict bound 2e + s < d and the code's "
                        + "minimum-distance condition force the candidates to coincide."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("alpha");
        Formula length = F.Id("n");
        Formula distance = F.Id("d");
        Formula errorBudget = F.Id("e");
        Formula erasureBudget = F.Id("s");
        Formula code = F.Id("C");
        Formula erased = F.Id("E");
        Formula trueWord = F.Id("c");
        Formula received = F.Id("r");
        Formula candidate = F.Id("x");
        Formula competitor = F.Id("y");
        Formula index = F.Id("i");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula indexType = Call("Fin", length);
        Formula wordType = Seq(indexType, Sp, To, Sp, carrier);
        Formula candidateProperty = Seq(
            candidate, Sp, InMacro, Sp, code, Sp, Land, Sp,
            UnerasedErrorCount(erased, received, candidate, index, indexType),
            Sp, Leq, Sp, errorBudget);
        Formula competitorProperty = Seq(
            competitor, Sp, InMacro, Sp, code, Sp, Land, Sp,
            UnerasedErrorCount(erased, received, competitor, index, indexType),
            Sp, Leq, Sp, errorBudget);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, carrier, Colon, Sp, type, Comma, Sp,
                OpenBracket, Call("DecidableEq", carrier), CloseBracket, Comma),
            Seq(
                length, Comma, Sp, distance, Comma, Sp, errorBudget, Comma, Sp,
                erasureBudget, Sp, InMacro, Sp, naturals, Comma),
            Seq(
                code, Colon, Sp, Call("Set", wordType), Comma, Sp,
                erased, Colon, Sp, Call("Finset", indexType), Comma),
            Seq(
                trueWord, Comma, Sp, received, Colon, Sp, wordType, Comma),
            Seq(
                MinimumDistance(code, distance), Sp, Land, Sp,
                Call("card", erased), Sp, Leq, Sp, erasureBudget, Sp, Land),
            Seq(
                D(2), Sp, Times, Sp, errorBudget, Sp, Plus, Sp, erasureBudget,
                Sp, Lt, Sp, distance, Sp, Land),
            Seq(
                trueWord, Sp, InMacro, Sp, code, Sp, Land, Sp,
                UnerasedErrorCount(erased, received, trueWord, index, indexType),
                Sp, Leq, Sp, errorBudget, Sp, Rightarrow),
            Seq(
                Exists, Sp, candidate, Colon, Sp, wordType, Comma, Sp,
                Open, candidateProperty, Close, Sp, Land),
            Seq(
                Forall, Sp, competitor, Colon, Sp, wordType, Comma, Sp,
                Open, competitorProperty, Close, Sp, Rightarrow, Sp,
                competitor, Sp, Eq, Sp, candidate, Dot),
        ]));
    }

    private static Formula UnerasedErrorCount(
        Formula erased,
        Formula received,
        Formula word,
        Formula index,
        Formula indexType)
    {
        Formula coordinates = Seq(
            OpenBrace, index, Colon, Sp, indexType, Sp, Mid, Sp,
            Neg, Open, index, Sp, InMacro, Sp, erased, Close, Sp, Land, Sp,
            Apply(received, index), Sp, Neq, Sp, Apply(word, index), CloseBrace);
        return Call("card", coordinates);
    }

    private static Formula MinimumDistance(Formula code, Formula distance) =>
        Call("MinDistanceAtLeast", code, distance);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
