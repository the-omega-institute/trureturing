using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class CommonPriorPosteriorAgreementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commonly known posteriors from a positive finite common prior agree.",
        H("Common-Prior Posterior Agreement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-knowledge-posteriors-agree"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationOrder/CommonPriorPosteriorAgreement."
                        + "common_knowledge_posteriors_agree"),
                H("Commonly known posterior values agree"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The world type is finite and mu is a strictly positive normalized common "
                            + "prior. The event E and nonempty common-knowledge cell K are finite "
                            + "subsets of that exact world carrier.")),
                    Paragraph(Text(
                        "Each information structure is a finite partition of K. This is the "
                            + "restriction of the agent's information partition to the common-"
                            + "knowledge cell; closure of a common-knowledge cell makes every such "
                            + "part a whole information cell.")),
                    Paragraph(Text(
                        "The posterior on a cell C is constructed as common-prior mass of E "
                            + "inside C divided by common-prior mass of C. Strict positivity and "
                            + "nonempty partition parts make every denominator positive.")),
                    Paragraph(Text(
                        "Summing the constant posterior identity over either partition gives the "
                            + "same event mass on K: a times mu(K) for the first agent and b times "
                            + "mu(K) for the second. Since mu(K) is positive, a equals b.")),
                    Paragraph(Text(
                        "Repository and pinned Mathlib searches found no exact common-prior "
                            + "agreement theorem. The proof directly applies Mathlib's canonical "
                            + "finite-partition union and disjoint-sum machinery."))),
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

    private static Formula TheoremFormula()
    {
        Formula worlds = Omega;
        Formula prior = Mu;
        Formula eventSet = F.Id("E");
        Formula commonCell = F.Id("K");
        Formula firstPartition = Subscript(Pi, D(1));
        Formula secondPartition = Subscript(Pi, D(2));
        Formula firstPosterior = F.Id("a");
        Formula secondPosterior = F.Id("b");
        Formula world = F.Id("w");
        Formula cell = F.Id("C");
        Formula mass = Call("mass", cell);
        Formula eventMass = Call("eventMass", eventSet, cell);
        Formula posterior = Call("post", eventSet, cell);
        Formula posteriorDefinition = Seq(
            Call("mass", cell), Sp, Eq, Sp,
            Sum, Underscore, Grp(world, Sp, InMacro, Sp, cell), Sp,
            Call("apply", prior, world), Comma, Sp,
            eventMass, Sp, Eq, Sp,
            Sum, Underscore, Grp(
                world, Sp, InMacro, Sp, cell, Comma, Sp,
                world, Sp, InMacro, Sp, eventSet), Sp,
            Call("apply", prior, world), Comma, Sp,
            posterior, Sp, Eq, Sp, Frac, Grp(eventMass), Grp(mass));
        Formula firstCommon = Seq(
            Forall, Sp, cell, Sp, InMacro, Sp, Call("parts", firstPartition),
            Comma, Sp, posterior, Sp, Eq, Sp, firstPosterior);
        Formula secondCommon = Seq(
            Forall, Sp, cell, Sp, InMacro, Sp, Call("parts", secondPartition),
            Comma, Sp, posterior, Sp, Eq, Sp, secondPosterior);

        return Disp(Seq(
            Call("Finite", worlds), Comma, Sp,
            OpenBracket, Call("DecidableEq", worlds), CloseBracket, Comma, Sp,
            prior, Colon, Sp, worlds, Sp, To, Sp, Mathbb, Grp(F.Id("R")),
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, world, Sp, InMacro, Sp, worlds, Comma, Sp,
            D(0), Sp, Lt, Sp, Call("apply", prior, world), Close,
            Comma, Sp, Sum, Underscore, Grp(world, Sp, InMacro, Sp, worlds), Sp,
            Call("apply", prior, world), Sp, Eq, Sp, D(1), Comma, RowBreak, Grp(),
            eventSet, Comma, Sp, commonCell, Sp, Subseteq, Sp, worlds,
            Comma, Sp, commonCell, Sp, Neq, Sp, Emptyset, Comma, RowBreak, Grp(),
            firstPartition, Comma, Sp, secondPartition, Sp, InMacro, Sp,
            Call("Finpartition", commonCell), Comma, RowBreak, Grp(),
            posteriorDefinition, Comma, RowBreak, Grp(),
            firstCommon, Comma, RowBreak, Grp(),
            secondCommon, RowBreak, Grp(),
            Rightarrow, Sp, firstPosterior, Sp, Eq, Sp, secondPosterior, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
