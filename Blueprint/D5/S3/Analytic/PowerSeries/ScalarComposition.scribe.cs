using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PowerSeries;

internal sealed class ScalarCompositionDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Scalars(Formula body) =>
        All("K", Call("Type"), All("E", Call("Type"), Seq(
            OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp,
            OpenBracket, Call("Ring", F.Id("E")), CloseBracket, Sp,
            OpenBracket, Call("Algebra", F.Id("K"), F.Id("E")), CloseBracket, Sp,
            OpenBracket, Call("TopologicalSpace", F.Id("E")), CloseBracket, Sp,
            OpenBracket, Call("IsTopologicalRing", F.Id("E")), CloseBracket, Sp, body)));

    private static Formula Evaluation() => Scalars(
        All("P", Call("PowerSeries", F.Id("K")),
        All("n", F.Id("Nat"),
        All("v", new Formula.TypeArrow(Call("Fin", F.Id("n")), F.Id("E")), Seq(
            Call("toFMS", F.Id("E"), F.Id("P"), F.Id("n"), F.Id("v")), Sp, Eq, Sp,
            Call("smul", Call("coeff", F.Id("n"), F.Id("P")),
                Call("prod", Call("ofFn", F.Id("v")))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar substitution and multilinear composition agree over a topological ring algebra.",
        H("Ordered scalar composition"),
        Blocks(
            Describe.Lean(DescribeId.Create("scalar-realization"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS"),
                H("Realization of a scalar coefficient series"),
                StatementSource.FromAuthor(Disp(Evaluation())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/AnalyticClosure/miyahara2026scalarcomposition")),
                Blocks(Paragraph(Text("For a field K and a possibly noncommutative ring E with a K-algebra structure, topology and topological-ring structure, the degree n term acts on a vector v by multiplying its entries in order and scaling by the nth coefficient. Empty products give the degree-zero term. This is FormalMultilinearSeries.ofScalars applied to the coefficient function."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("scalar-evaluation"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS_apply"),
                H("Evaluation on an arbitrary vector"),
                StatementSource.FromAuthor(Disp(Evaluation())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/AnalyticClosure/miyahara2026scalarcomposition")),
                Blocks(Paragraph(Text("This evaluation formula includes every natural degree and every vector in Fin n to E. No commutativity of multiplication in E is required."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("scalar-substitution-composition"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS_subst"),
                H("Substitution realizes composition"),
                StatementSource.FromAuthor(Disp(Scalars(
                    All("P", Call("PowerSeries", F.Id("K")),
                    All("Q", Call("PowerSeries", F.Id("K")), Seq(
                        Call("HasSubst", F.Id("P")), Sp, Implies, Sp,
                        Call("toFMS", F.Id("E"), Call("subst", F.Id("P"), F.Id("Q"))),
                        Sp, Eq, Sp,
                        Call("comp", Call("toFMS", F.Id("E"), F.Id("Q")),
                            Call("toFMS", F.Id("E"), F.Id("P"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/AnalyticClosure/miyahara2026scalarcomposition")),
                Blocks(
                    Paragraph(Text("The inner series P has nilpotent constant coefficient, expressed by HasSubst P. Over a field this coefficient is zero. Bare subst P Q means outer Q after inner P, matching the order of the two multilinear series on the right.")),
                    Paragraph(Text("In each fixed degree, terms containing a zero-sized inner block vanish. The remaining finitely many positive block partitions correspond to compositions of that degree. Flattening these blocks preserves the order of the input vector. Scalar multiplication distributes through that ordered product by the algebra action laws, including for a noncommutative target ring.")),
                    Paragraph(Text("The correspondence concerns formal series. To identify the coefficients of an analytic inverse, one must also supply an actual inverse germ, convergent expansions of the two functions, and one-dimensional uniqueness. It supplies no convergence radius or value at a specified endpoint."))),
                DescribeRole.Theorem))));
}
