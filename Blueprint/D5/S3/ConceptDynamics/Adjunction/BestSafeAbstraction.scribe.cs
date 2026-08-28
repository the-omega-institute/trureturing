using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Adjunction;

internal sealed class BestSafeAbstractionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Adjunction/BestSafeAbstraction.best_safe_abstraction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Galois-derived transformer is safe and pointwise most precise among safe abstractions.",
        H("Best Safe Abstraction"),
        Blocks(Describe.Lean(
            DescribeId.Create("galois-derived-transformer-is-best-safe-abstraction"),
            DeclarationHandle.Create(Declaration),
            H("The Galois-derived transformer is the best safe abstraction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public canonical transformer first concretizes an abstract state, "
                        + "takes the direct image under the concrete process, and abstracts the "
                        + "result.")),
                Paragraph(Text(
                    "The unit of the Galois connection proves safety. Applying the adjunction "
                        + "to any other safe transformer proves that the canonical transformer "
                        + "is pointwise below it, hence at least as precise."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Compose(params Formula[] functions)
    {
        var items = new List<Formula>();
        for (var index = 0; index < functions.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Sp);
                items.Add(Circ);
                items.Add(Sp);
            }

            items.Add(functions[index]);
        }

        return Seq([.. items]);
    }

    private static Formula Safety(
        Formula process,
        Formula concretization,
        Formula transformer,
        Formula abstractState) =>
        Seq(
            Call("image", process, Apply(concretization, abstractState)),
            Sp, Subseteq, Sp,
            Apply(concretization, Apply(transformer, abstractState)));

    private static Formula TheoremFormula()
    {
        Formula concrete = F.Id("X");
        Formula abstractCarrier = F.Id("A");
        Formula abstraction = Alpha;
        Formula concretization = GammaLower;
        Formula process = F.Id("F");
        Formula best = F.Id("Fbest");
        Formula candidate = F.Id("Gsharp");
        Formula abstractState = F.Id("a");
        Formula setConcrete = Call("Set", concrete);
        Formula canonical = Compose(abstraction, Call("image", process), concretization);

        return Disp(Seq(
            Forall, Sp, concrete, Comma, Sp, abstractCarrier, Colon, Sp, F.Id("Type"),
            Comma, Sp, Call("Preorder", abstractCarrier), Comma, Sp,
            abstraction, Colon, Sp, setConcrete, Sp, To, Sp, abstractCarrier, Comma, Sp,
            concretization, Colon, Sp, abstractCarrier, Sp, To, Sp, setConcrete, Comma, Sp,
            process, Colon, Sp, concrete, Sp, To, Sp, concrete, Comma, RowBreak, Grp(),
            Call("GaloisConnection", abstraction, concretization), Sp, Rightarrow, Sp,
            F.Id("let"), Sp, best, Colon, Sp,
            abstractCarrier, Sp, To, Sp, abstractCarrier, Sp, Colon, Eq, Sp,
            canonical, Comma, RowBreak, Grp(),
            Open, Forall, Sp, abstractState, Colon, Sp, abstractCarrier, Comma, Sp,
            Safety(process, concretization, best, abstractState), Close, Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, candidate, Colon, Sp,
            abstractCarrier, Sp, To, Sp, abstractCarrier, Comma, Sp,
            Open, Forall, Sp, abstractState, Colon, Sp, abstractCarrier, Comma, Sp,
            Safety(process, concretization, candidate, abstractState), Close,
            Sp, Rightarrow, Sp,
            Forall, Sp, abstractState, Colon, Sp, abstractCarrier, Comma, Sp,
            Apply(best, abstractState), Sp, Leq, Sp,
            Apply(candidate, abstractState), Dot));
    }
}
