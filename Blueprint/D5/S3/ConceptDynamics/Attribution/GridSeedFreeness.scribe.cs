using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class GridSeedFreenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime divisibility characterizes freeness in every law calibrating a complete grid.",
        H("When every calibrating seed action is free"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-grid-seed-freeness"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/GridSeedFreeness.every_calibrating_law_free_iff"),
            H("Prime divisibility is necessary and sufficient"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let k and m be natural numbers with m positive. The input profiles are all "
                    + "natural vectors on k labels with total m. EveryCalibratingLawFree means "
                    + "every finite positive calibrating law on these profiles has trivial "
                    + "stabilizer at every seed. PrimeDivisibility means every prime at most k "
                    + "divides m.")),
                Paragraph(Text(
                    "If each prime at most k divides m, multiply the seed weights by m and apply "
                    + "the prime-cycle obstruction to the resulting unnormalized masses. A "
                    + "nontrivial seed stabilizer would contain an element of prime order.")),
                Paragraph(Text(
                    "If a prime p at most k fails to divide m, choose a single p-cycle on the "
                    + "labels. For a profile fixed by the cycle, the total count on the cycle is "
                    + "a multiple of p, so a positive coordinate exists outside its support. "
                    + "For other profiles the associated subgroup of prime order has trivial "
                    + "input stabilizer, so any positive coordinate is allowed. At every profile "
                    + "a positive output is fixed by the elements of the cyclic subgroup that "
                    + "fix that profile. The resulting calibrating "
                    + "law has a positive seed fixed by the chosen nonidentity cycle."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        return Disp(Seq(Forall, Sp, k, Sp, m, Comma, Sp, D(0), Sp, Lt, Sp, m,
            Sp, Rightarrow, Sp, Open, Call("EveryCalibratingLawFree", k, m), Sp,
            Iff, Sp, Call("PrimeDivisibility", k, m), Close));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
