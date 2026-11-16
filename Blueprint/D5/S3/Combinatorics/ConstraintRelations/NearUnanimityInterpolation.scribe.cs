using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ConstraintRelations;

internal sealed class NearUnanimityInterpolationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Computability/bartokrokhinwillard2017polymorphisms");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single fixed near-unanimity operation interpolates every finite coordinate set from smaller projections.",
        H("Finite-coordinate near-unanimity interpolation"), Blocks(
            Paragraph(Text("Let I be any type in universe u and X(i) any family of types in an independent universe v. Tuple(X) denotes the dependent product of the X(i). Operations(X,k) denotes the family of functions nu(i) from (Fin(k) to X(i)) to X(i). Neither I nor any X(i) is required to be finite.")),
            Paragraph(Text("For tuples r and theta and a finite coordinate set T, Agree(r,theta,T) means that r(i)=theta(i) for every i in T. For values a,b in X(i) and bad in Fin(k), OneException(a,b,bad) is the function taking value b at bad and a at every other index. Combine(nu,rows) is the tuple whose ith coordinate is nu(i) applied to the k values rows(j)(i).")),
            Paragraph(Text("The near-unanimity law and coordinatewise preservation have the following full meanings:")),
            Paragraph(Math(Disp(NearUnanimity()))),
            Paragraph(Math(Disp(Preservation()))),
            Describe.Lean(
                DescribeId.Create("fixed-arity-near-unanimity-finite-coordinate-interpolation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/ConstraintRelations/NearUnanimityInterpolation.finite_coordinate_interpolation"),
                H("Interpolation on a finite coordinate set"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Here NULaw and Preserves denote exactly the two displayed conditions. Every small projection witness is an actual member of R. In particular T may be empty: its hypothesis requires R to be nonempty. Empty F is included. The operation has this one fixed arity k; a family of operations at all arities is not assumed. There is no assumption of symmetry, associativity or coherent choices of local witnesses.")),
                    Paragraph(Text("Proof by strong induction on the finite coordinate set F. If its size is less than k, take the supplied local witness for F itself. Otherwise choose k distinct elements of F. For each chosen element, induction gives a member of R agreeing with theta after deleting that element. Closure places the coordinatewise combination of these k members in R. At any coordinate of F at most one chosen deletion can remove that coordinate. All other rows therefore have value theta there, and the near-unanimity law makes the combination equal theta at that coordinate.")),
                    Paragraph(Text("Example 72, pages 34–35, of Barto, Krokhin and Willard gives the classical subpower generation mechanism for a common carrier. The proof here establishes the stated dependent-coordinate finite interpolation theorem. When I is infinite, interpolation on every finite F is not a claim that theta itself belongs to R. No compactness or infinite-coordinate extension is assumed."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Fn(Formula a, Formula b) => Seq(Par(a), To, Par(b));
    private static Formula Tuple => Call("Tuple", F.Id("X"));
    private static Formula Index => F.Id("I");
    private static Formula Arity => Call("Fin", F.Id("k"));
    private static Formula NearUnanimity() => All("i", Index,
        All("a", Call("X", F.Id("i")), All("b", Call("X", F.Id("i")), All("bad", Arity,
            Rel(Call("nu", F.Id("i"), Call("OneException", F.Id("a"), F.Id("b"), F.Id("bad"))),
                FormulaRelationOperator.Equal, F.Id("a"))))));
    private static Formula Preservation() => All("rows", Fn(Arity, Tuple),
        Imp(All("j", Arity, Rel(Call("rows", F.Id("j")), FormulaRelationOperator.MemberOf, F.Id("R"))),
            Rel(Call("Combine", F.Id("nu"), F.Id("rows")), FormulaRelationOperator.MemberOf, F.Id("R"))));
    private static Formula Interpolates(Formula coordinates) => Ex("r", Tuple,
        And(Rel(F.Id("r"), FormulaRelationOperator.MemberOf, F.Id("R")),
            Call("Agree", F.Id("r"), F.Id("theta"), coordinates)));
    private static Formula Statement()
    {
        var small = All("T", Call("Finset", Index),
            Imp(And(Rel(F.Id("T"), FormulaRelationOperator.SubsetOf, F.Id("F")),
                Rel(Call("card", F.Id("T")), FormulaRelationOperator.LessThan, F.Id("k"))),
                Interpolates(F.Id("T"))));
        return All("I", Call("Type", F.Id("u")),
            All("X", Fn(Index, Call("Type", F.Id("v"))),
            All("k", Call("Nat"),
            All("nu", Call("Operations", F.Id("X"), F.Id("k")),
            All("R", Call("Set", Tuple), All("theta", Tuple,
            All("F", Call("Finset", Index),
                Imp(And(Rel(D(3), FormulaRelationOperator.LessThanOrEqual, F.Id("k")),
                    And(Call("NULaw", F.Id("nu")), And(Call("Preserves", F.Id("nu"), F.Id("R")), small))),
                    Interpolates(F.Id("F"))))))))));
    }
}
