using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class MultiTargetInformationChainDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Entropy/Observation/MultiTargetInformationChain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The total finite information cost of adjoining a heterogeneous target family is "
            + "independent of its order and is the sum of ordered conditional contributions.",
        H("Multi-Target Information Chain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("multi-target-information-chain"),
                DeclarationHandle.Create(DeclarationPrefix + "multi_target_information_chain"),
                H("Total target information is independent of target order"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each target value is tagged by its original finite index and placed after "
                            + "the concept readout in the repository's recursive FutureWord "
                            + "carrier. "
                            + "A permutation changes only the target coordinates and fixes the "
                            + "initial concept coordinate.")),
                    Paragraph(Text(
                        "The frozen finite-word chain rule expands the permuted law into one "
                            + "full-prefix conditional entropy for each target. Entropy invariance "
                            + "under the induced coordinate equivalence identifies its total cost "
                            + "with the canonical target order.")),
                    Paragraph(Text(
                        "The PMF binder supplies the finite probability model. No common target "
                            + "codomain is assumed: the family Y may vary with the target "
                            + "index."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Define(Formula name, Formula value) =>
        Seq(name, Sp, Colon, Eq, Sp, value);

    private static Formula Entropy(Formula law) =>
        Call("H", law);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula n = F.Id("n");
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetFamily = F.Id("Y");
        Formula index = F.Id("i");
        Formula mass = F.Id("mu");
        Formula concept = F.Id("C");
        Formula targets = F.Id("T");
        Formula permutation = F.Id("pi");
        Formula canonicalLaw = new Formula.Subscript(F.Id("p"), D(0));
        Formula permutedLaw = new Formula.Subscript(F.Id("p"), permutation);
        Formula finiteIndex = Call("Fin", n);
        Formula targetAtIndex = Seq(targetFamily, Open, index, Close);
        Formula finiteTargets = Seq(
            Forall, Sp, Typed(index, finiteIndex), Comma, Sp,
            Call("Fintype", targetAtIndex));
        Formula targetReadouts = Seq(
            Forall, Sp, Typed(index, finiteIndex), Comma, Sp,
            Arrow(state, targetAtIndex));
        Formula canonicalDefinition = Call(
            "orderedCompletionLaw", mass, concept, targets, Call("refl", finiteIndex));
        Formula permutedDefinition = Call(
            "orderedCompletionLaw", mass, concept, targets, permutation);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(n, naturals), Comma, Sp,
            Typed(Seq(state, Comma, Sp, conceptType), type), Comma, RowBreak, Grp(),
            Typed(targetFamily, Arrow(finiteIndex, type)), Comma, RowBreak, Grp(),
            Open, Call("Fintype", state), Sp, Land, Sp,
            Call("Fintype", conceptType), Sp, Land, Sp, finiteTargets, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, Typed(mass, Call("PMF", state)), Comma, Sp,
            Typed(concept, Arrow(state, conceptType)), Comma, RowBreak, Grp(),
            Typed(targets, targetReadouts), Comma, RowBreak, Grp(),
            Typed(permutation, Call("Perm", finiteIndex)), Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            Define(canonicalLaw, canonicalDefinition), Comma, RowBreak, Grp(),
            Define(permutedLaw, permutedDefinition), RowBreak, Grp(),
            Operatorname, Grp(F.Id("in")), Sp,
            Entropy(canonicalLaw), Sp, Minus, Sp,
            Entropy(Call("firstReadoutMarginal", canonicalLaw)), Sp, Eq, Sp,
            Sum, Underscore, Grp(F.Id("k"), Sp, Lt, Sp, n), Sp,
            Call("prefixConditionalEntropy", permutedLaw, F.Id("k")), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
