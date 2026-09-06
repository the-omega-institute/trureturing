using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class QueryFamilyIdentificationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dependent query family identifies exactly the targets constant on its joint "
            + "kernel, equivalently those descending uniquely to the query quotient.",
        H("Query Family Identification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("query-kernel"),
                DeclarationHandle.Create(DeclarationPrefix + "queryKernel"),
                H("The query kernel is simultaneous answer equality"),
                StatementSource.FromAuthor(QueryKernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a dependent query family Q, two models lie in its kernel exactly "
                        + "when Q_i gives equal answers on the two models for every index i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("identification-is-query-kernel-inclusion"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "identification_iff_kernel_inclusion"),
                H("Identification is query-kernel inclusion"),
                StatementSource.FromAuthor(KernelInclusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The joint answer to a dependent query family is a dependent function "
                            + "whose component at an index is the answer to that query. Two "
                            + "models have the same joint answer exactly when every component "
                            + "answer agrees.")),
                    Paragraph(Text(
                        "Consequently the family identifies a target exactly when agreement "
                            + "under every query forces agreement under the target. This is the "
                            + "inclusion of the simultaneous query kernel in the target kernel, "
                            + "with no nonemptiness assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-dependent-joint-connects-to-single-interface-sufficiency"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "identification_iff_joint_refinement"),
                H("The dependent joint connects to single-interface sufficiency"),
                StatementSource.FromAuthor(JointRefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When the model space is nonempty, the whole dependent answer tuple is "
                            + "an ordinary single interface. The existing universal sufficiency "
                            + "factorization theorem applied to that joint interface identifies "
                            + "its fiber criterion with refinement of the canonical target "
                            + "readout.")),
                    Paragraph(Text(
                        "This bridge is the reuse point from the earlier single-interface result. "
                            + "The dependent answer type causes no obstruction because a dependent "
                            + "function space is still one Lean type."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nonempty-models-are-necessary-for-global-joint-refinement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nonempty_is_necessary_for_joint_refinement"),
                H("Nonempty models are necessary for global joint refinement"),
                StatementSource.FromAuthor(NonemptyNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let both the model type and query index type be empty, use Unit as the "
                            + "answer type, and take the target value type to be empty. Kernel "
                            + "identification is vacuous because there are no models.")),
                    Paragraph(Text(
                        "The joint answer type is nevertheless inhabited by its unique empty "
                            + "function, while the canonical target image is empty. No map from "
                            + "all joint answers to that target image can exist, so refinement "
                            + "fails. This isolates the exact role of the nonempty hypothesis."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("factorization-through-the-query-quotient-is-unique"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "quotient_factorization_unique"),
                H("Factorization through the query quotient is unique"),
                StatementSource.FromAuthor(FactorizationUniqueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose two maps from the query quotient recover the same target after "
                            + "composition with the canonical projection. Every quotient class "
                            + "has a model representative, so evaluation at a representative "
                            + "shows the two maps agree on that class.")),
                    Paragraph(Text(
                        "The proof needs no identification hypothesis once both factorizations "
                            + "are supplied. Surjectivity of the quotient projection alone gives "
                            + "uniqueness, including for an empty model space."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("identification-is-unique-query-quotient-factorization"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "identification_iff_unique_quotient_factorization"),
                H("Identification is unique query-quotient factorization"),
                StatementSource.FromAuthor(UniqueFactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Kernel inclusion makes the target constant on every query-equivalence "
                            + "class, so the library quotient lift defines a target readout on "
                            + "the quotient. Its composition with the projection is the original "
                            + "target.")),
                    Paragraph(Text(
                        "Conversely, any such factorization sends query-equivalent models to the "
                            + "same target value because their quotient classes agree. The "
                            + "surjectivity lemma supplies uniqueness, yielding the claimed "
                            + "unique factorization without extra instances."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula DependentQueryType(
        Formula indexType,
        Formula modelType,
        Formula answerFamily,
        Formula index) =>
        Seq(
            Open, Typed(index, indexType), Close, Sp, To, Sp,
            modelType, Sp, To, Sp, Apply(answerFamily, index));

    private static Formula QueryKernelFormula()
    {
        Formula model = F.Id("M");
        Formula indexType = F.Id("I");
        Formula answerFamily = F.Id("A");
        Formula queries = F.Id("Q");
        Formula index = F.Id("i");
        Formula first = F.Id("m");
        Formula second = F.Id("n");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(model, Comma, Sp, indexType), TypeUniverse()), Comma, RowBreak, Grp(),
            Typed(answerFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(queries, DependentQueryType(indexType, model, answerFamily, index)),
            Comma, Sp, Typed(Seq(first, Comma, Sp, second), model), Comma, RowBreak, Grp(),
            Apply(F.Id("queryKernel"), queries, first, second), Sp, Iff, Sp,
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Apply(queries, index, first), Sp, Eq, Sp,
            Apply(queries, index, second), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula KernelInclusionFormula()
    {
        Formula model = F.Id("M");
        Formula indexType = F.Id("I");
        Formula targetType = F.Id("Z");
        Formula answerFamily = F.Id("A");
        Formula queries = F.Id("Q");
        Formula target = F.Id("T");
        Formula index = F.Id("i");
        Formula first = F.Id("m");
        Formula second = F.Id("n");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(model, Comma, Sp, indexType, Comma, Sp, targetType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(answerFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(
                queries,
                DependentQueryType(indexType, model, answerFamily, index)),
            Comma, Sp, Typed(target, Arrow(model, targetType)), Comma, RowBreak, Grp(),
            Apply(F.Id("IdentifiedBy"), queries, target), Sp, Leftrightarrow, Sp,
            Forall, Sp, Typed(Seq(first, Comma, Sp, second), model), Comma, Sp,
            Apply(F.Id("queryKernel"), queries, first, second), Sp, Rightarrow, Sp,
            Apply(target, first), Sp, Eq, Sp, Apply(target, second), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula JointRefinementFormula()
    {
        Formula model = F.Id("M");
        Formula indexType = F.Id("I");
        Formula targetType = F.Id("Z");
        Formula answerFamily = F.Id("A");
        Formula queries = F.Id("Q");
        Formula target = F.Id("T");
        Formula index = F.Id("i");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(model, Comma, Sp, indexType, Comma, Sp, targetType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(answerFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(
                queries,
                DependentQueryType(indexType, model, answerFamily, index)),
            Comma, Sp, Typed(target, Arrow(model, targetType)), Comma, RowBreak, Grp(),
            Apply(F.Id("Nonempty"), model), Sp, Rightarrow, Sp,
            Open, Apply(F.Id("IdentifiedBy"), queries, target), Sp,
            Leftrightarrow, Sp,
            Apply(
                F.Id("Refines"),
                Apply(F.Id("canonicalTargetReadout"), target),
                Apply(F.Id("jointQuery"), queries)),
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula NonemptyNecessityFormula()
    {
        Formula queries = F.Id("Q");
        Formula target = F.Id("T");
        Formula index = F.Id("i");
        Formula empty = Emptyset;
        Formula unit = F.Id("Unit");
        Formula queryType = Seq(
            Open, Typed(index, empty), Close, Sp, To, Sp,
            empty, Sp, To, Sp, unit);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Typed(queries, queryType), Comma, Sp,
            Typed(target, Arrow(empty, empty)), Comma, RowBreak, Grp(),
            Apply(F.Id("IdentifiedBy"), queries, target), Sp, Land, RowBreak, Grp(),
            Neg, Sp,
            Apply(
                F.Id("Refines"),
                Apply(F.Id("canonicalTargetReadout"), target),
                Apply(F.Id("jointQuery"), queries)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FactorizationUniqueFormula()
    {
        Formula model = F.Id("M");
        Formula indexType = F.Id("I");
        Formula targetType = F.Id("Z");
        Formula answerFamily = F.Id("A");
        Formula queries = F.Id("Q");
        Formula target = F.Id("T");
        Formula index = F.Id("i");
        Formula first = F.Id("f");
        Formula second = F.Id("g");
        Formula quotient = Apply(F.Id("QueryQuotient"), queries);
        Formula projection = Apply(F.Id("queryQuotientProjection"), queries);
        Formula firstFactors = Seq(target, Sp, Eq, Sp, first, Sp, Circ, Sp, projection);
        Formula secondFactors = Seq(target, Sp, Eq, Sp, second, Sp, Circ, Sp, projection);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(model, Comma, Sp, indexType, Comma, Sp, targetType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(answerFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(
                queries,
                DependentQueryType(indexType, model, answerFamily, index)),
            Comma, Sp, Typed(target, Arrow(model, targetType)), Comma, RowBreak, Grp(),
            Typed(
                Seq(first, Comma, Sp, second),
                Arrow(quotient, targetType)),
            Comma, RowBreak, Grp(),
            Open, firstFactors, Sp, Land, Sp, secondFactors, Close,
            Sp, Rightarrow, Sp, first, Sp, Eq, Sp, second, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula UniqueFactorizationFormula()
    {
        Formula model = F.Id("M");
        Formula indexType = F.Id("I");
        Formula targetType = F.Id("Z");
        Formula answerFamily = F.Id("A");
        Formula queries = F.Id("Q");
        Formula target = F.Id("T");
        Formula index = F.Id("i");
        Formula factor = F.Id("f");
        Formula quotient = Apply(F.Id("QueryQuotient"), queries);
        Formula projection = Apply(F.Id("queryQuotientProjection"), queries);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(model, Comma, Sp, indexType, Comma, Sp, targetType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(answerFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(
                queries,
                DependentQueryType(indexType, model, answerFamily, index)),
            Comma, Sp, Typed(target, Arrow(model, targetType)), Comma, RowBreak, Grp(),
            Apply(F.Id("IdentifiedBy"), queries, target), Sp, Leftrightarrow, Sp,
            Exists, Bang, Sp,
            Typed(factor, Arrow(quotient, targetType)), Comma, Sp,
            target, Sp, Eq, Sp, factor, Sp, Circ, Sp, projection, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
