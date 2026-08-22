using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class FactorizationCategoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement factorization composes, is reflexive, and has preorder and category readings.",
        H("Refinement Factorization Category"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinement-factorization-structure"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/FactorizationCategory."
                        + "refinement_factorization_structure"),
                H("Refinement factorization composes and supports both readings"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A refinement is the source factorization data itself: a map from the "
                            + "finer readout codomain to the coarser codomain together with a "
                            + "pointwise commuting equality. The identity map supplies reflexivity, "
                            + "and composing the two factor maps supplies transitivity.")),
                    Paragraph(Text(
                        "Readouts are constructed from their actual source and codomain types. "
                            + "The quotient carrier identifies readouts exactly when a codomain "
                            + "isomorphism carries one readout to the other; refinement is "
                            + "transported across those representatives, yielding the stated "
                            + "preorder relation.")),
                    Paragraph(Text(
                        "Without quotienting, the same factorization data forms a category: the "
                            + "public structure includes identities, composition, both identity "
                            + "laws, and associativity. Repository search found no exact theorem "
                            + "packaging all of these clauses; the canonical Concept readout "
                            + "carrier is imported directly."))),
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

    private static Formula FactorizationFormula()
    {
        Formula source = F.Id("X");
        Formula codomainTwo = F.Id("Btwo");
        Formula codomainOne = F.Id("Bone");
        Formula codomainZero = F.Id("Bzero");
        Formula second = F.Id("qTwo");
        Formula first = F.Id("qOne");
        Formula coarse = F.Id("qZero");
        Formula readout = F.Id("q");
        Formula quotient = F.Id("Q");
        Formula category = F.Id("C");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula concept = Call("Concept", source, codomainZero);
        Formula refinement = Call("Refines", first, coarse);
        Formula secondRefinement = Call("Refines", second, first);
        Formula composite = Call("Refines", second, coarse);
        Formula reflexive = Call("Nonempty", Call("Refines", coarse, coarse));
        Formula transitive = Seq(
            Call("Nonempty", refinement), Sp, Rightarrow, Sp,
            Call("Nonempty", secondRefinement), Sp, Rightarrow, Sp,
            Call("Nonempty", composite));
        Formula quotientWitness = Call(
            "Nonempty", Call("PreorderWitness", Call("QuotientCodomainClass", source)));
        Formula categoryWitness = Call(
            "Nonempty", Call("FactorizationCategoryReading", source));

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, codomainTwo, Comma, Sp, codomainOne,
            Comma, Sp, codomainZero, Colon, Sp, type, Comma, Esc,
            second, Comma, Sp, first, Comma, Sp, coarse, Colon, Sp,
            concept, Comma, Esc,
            Open, reflexive, Sp, Land, Sp, Open, transitive, Close, Close,
            Sp, Land, Sp, quotientWitness, Sp, Land, Sp, categoryWitness, Dot));
    }
}
