using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PresburgerEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient normalization and finite periodic tests preserve existential semantics.", H("Eliminating one integer coordinate"),
        Blocks(Paragraph(Text("Affine.substHead replaces the first coordinate by an affine expression on the remaining coordinates. eval_head decomposes a value as head*x+tail.eval(xs). Both affine and atom substitution preserve evaluation at replacement.eval(xs)::xs.")),
            Paragraph(Text("Cooper.commonCoefficient is a positive common multiple of the nonzero head coefficient magnitudes. Normalization replaces x by y=L*x and scales each nonzero coefficient to its sign. Divisibility moduli scale by the same positive quotient; zero head coefficients retain their fixed values. normalizeClause adds the atom L divides y, so the reverse direction can recover an integer x. Normal inequalities have head coefficient -1, 0 or 1.")),
            Paragraph(Text("A normalized clause splits into fixed atoms, affine lower bounds, affine upper bounds and periodic divisibility atoms. The period is a positive common multiple of the moduli. Adding this period to the head value preserves all periodic atoms, including nondivisibility. eval_normalizedClause_iff states the conjunction of the fixed test, all lower bounds, all upper bounds and the periodic test. Empty lists are handled by their ordinary all/any semantics.")),
            Paragraph(Text("boundedPair enumerates k in List.range m and checks lo+k<=hi together with the periodic clause at lo+k. elimVariable uses the one-sided residue disjunction when a bound list is empty and the conjunction of pair tests otherwise. elimNormalizedClause also retains fixed atoms. elimClause first normalizes; eliminate distributes this procedure over positive DNF. The finite residue enumeration is the upstream Cooper algorithm.")),
            Describe.Lean(DescribeId.Create("normalizeclause-exists-iff"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerElimination.normalizeClause_exists_iff"),
            H("Normalization preserves existence"), StatementSource.FromAuthor(F.Disp(A("c", V("Clause"), A("xs", Call("List", V("Int")), I(X("x", V("Int"), E(Call("evalClause",V("c"),Call("cons",V("x"),V("xs"))),V("true"))), X("y", V("Int"), E(Call("evalClause",Call("normalizeClause",V("c")),Call("cons",V("y"),V("xs"))),V("true")))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("The forward proof substitutes y=L*x. The reverse proof uses the added divisibility atom to write y=L*x, then cancels the positive scaling factors in each inequality or divisibility test."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elimclause-correct"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerElimination.elimClause_correct"),
            H("Clause elimination"), StatementSource.FromAuthor(F.Disp(A("c", V("Clause"), A("xs", Call("List", V("Int")), I(E(Call("eval",Call("elimClause",V("c")),V("xs")),V("true")), X("x", V("Int"), E(Call("evalClause",V("c"),Call("cons",V("x"),V("xs"))),V("true")))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Normalization equivalence combines with elimNormalizedClause_correct. Fixed constraints are independent of the eliminated head; the periodic finite criterion supplies that head when the remaining tests hold."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eliminate-correct"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerElimination.eliminate_correct"),
            H("Quantifier-free elimination"), StatementSource.FromAuthor(F.Disp(A("p", V("QF"), A("xs", Call("List", V("Int")), I(E(Call("eval",Call("eliminate",V("p")),V("xs")),V("true")), X("x", V("Int"), E(Call("eval",V("p"),Call("cons",V("x"),V("xs"))),V("true")))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Polarity conversion identifies a satisfied clause in either direction. Applying elimClause_correct to that clause removes exactly one existential integer coordinate; the remaining valuation is unrestricted."))), DescribeRole.Theorem)), [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/PresburgerNormalForm")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/PresburgerCooper"))]));

    private static Formula V(string name) => F.Id(name);
    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula X(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula E(Formula left, Formula right) => F.Seq(left, F.Sp, F.Eq, F.Sp, right);
    private static Formula I(Formula left, Formula right) => F.Seq(F.Open, left, F.Close, F.Sp, F.Iff, F.Sp, F.Open, right, F.Close);
}
