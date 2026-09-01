using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class RamifiedConjugateJetDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Eigenstructure/RamifiedConjugateJet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A repeated residue eigenvalue retains the infinite power jet of its nilpotent part.",
        H("Ramified Conjugate Jet"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ramified-conjugate-jet"),
                DeclarationHandle.Create(Prefix + "ramifiedConjugateJet"),
                H("The ramified jet records every positive residual power"),
                StatementSource.FromAuthor(JetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The scalar center is followed by a natural-number-indexed sequence. "
                        + "Index zero stores the first residual power, so the definition is "
                        + "an infinite sequence rather than a truncated tuple."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-ramified-conjugate-jet-exists"),
                DeclarationHandle.Create(
                    Prefix + "exists_golden_ramified_conjugate_jet"),
                H("A nonzero square-zero direction realizes the golden ramified jet"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Over ZMod 5, the upper off-diagonal matrix N is nonzero, has rank "
                            + "one, and satisfies N squared equals zero. Translating it by "
                            + "three times the identity gives a matrix whose characteristic "
                            + "polynomial has three as a root of multiplicity two.")),
                    Paragraph(Text(
                        "The resulting jet has N as its index-zero term and N to the power "
                            + "k+1 at every index k. Square-zero nilpotence makes every term "
                            + "after index zero vanish, while preserving a nontrivial first "
                            + "direction.")),
                    Paragraph(Text(
                        "The proof reuses the repository's standard rank-one nilpotent matrix "
                            + "witness and Mathlib's two-by-two characteristic-polynomial and "
                            + "root-multiplicity theorems."))),
                DescribeRole.Theorem))));

    private static Formula JetFormula()
    {
        Formula matrix = F.Id("T");
        Formula center = F.Id("lambdaZero");
        Formula index = F.Id("k");
        Formula residual = Seq(
            Open, matrix, Sp, Minus, Sp, center, Sp, F.Id("I"), Close);
        Formula tail = Seq(
            Open, index, Sp, Mapsto, Sp,
            residual, Caret, Grp(index, Sp, Plus, Sp, D(1)), Close);
        return Disp(Seq(
            Call("RamJet", center, matrix), Sp, Eq, Sp,
            Open, center, Comma, Sp, tail, Close, Dot));
    }

    private static Formula WitnessFormula()
    {
        Formula matrix = F.Id("T");
        Formula nilpotent = F.Id("N");
        Formula index = F.Id("k");
        Formula field = Call("ZMod", D(5));
        Formula matrixSpace = Call("Matrix", D(2), field);
        Formula jetTail = Call("tail", Call("RamJet", D(3), matrix), index);
        Formula powerTail = Seq(
            Open, index, Sp, Mapsto, Sp,
            nilpotent, Caret, Grp(index, Sp, Plus, Sp, D(1)), Close);
        return Disp(new Formula.Aligned([
            Seq(
                Exists, Sp, nilpotent, Comma, Sp, matrix, Sp, InMacro, Sp,
                matrixSpace, Comma),
            Seq(
                nilpotent, Sp, Eq, Sp, Call("single", D(0), D(1), D(1)), Sp,
                Land, Sp, matrix, Sp, Eq, Sp, D(3), Sp, F.Id("I"), Sp, Plus, Sp,
                nilpotent, Comma),
            Seq(
                nilpotent, Sp, Neq, Sp, D(0), Sp, Land, Sp,
                nilpotent, Caret, Grp(D(2)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                Call("rank", nilpotent), Sp, Eq, Sp, D(1), Comma),
            Seq(
                Call("charpoly", matrix), Sp, Eq, Sp,
                Open, F.Id("X"), Sp, Minus, Sp, D(3), Close,
                Caret, Grp(D(2)), Sp, Land, Sp,
                Call("rootMultiplicity", D(3), Call("charpoly", matrix)),
                Sp, Eq, Sp, D(2), Comma),
            Seq(
                Call("RamJet", D(3), matrix), Sp, Eq, Sp,
                Open, D(3), Comma, Sp, powerTail, Close, Comma),
            Seq(
                Call("tail", Call("RamJet", D(3), matrix), D(0)),
                Sp, Eq, Sp, nilpotent, Sp, Land, Sp,
                Forall, Sp, index, Sp, Geq, Sp, D(1), Comma, Sp,
                jetTail, Sp, Eq, Sp, D(0), Dot),
        ]));
    }
}
