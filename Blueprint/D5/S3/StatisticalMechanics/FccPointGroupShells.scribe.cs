using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class FccPointGroupShellsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/FccPointGroupShells";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/conwaysloane1997a008368");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed coordinate permutation orbits on every contact shell of the face centered cubic "
            + "lattice have generating function (1−X⁵)/((1−X)(1−X²)²(1−X³)).",
        H("Point-group orbits on face centered cubic shells"),
        Blocks(
            Definition("lattice", "L", "The even-sum lattice", LatticeFormula(),
                "Coordinates are indexed by Fin 3, namely zero, one and two. The coordinate sum is even. "
                    + "This is the integer realization of the face centered cubic lattice D3."),
            Definition("contacts", "contactGraph", "The twelve contact steps", ContactFormula(),
                "An edge changes exactly two distinct coordinates by one in absolute value and fixes the "
                    + "third. Each of the three choices of a coordinate pair has four sign choices. "
                    + "Both endpoints belong to the lattice."),
            Definition("origin", "origin", "The specified center", All("i", Call("Fin", D(3)), Eq(App(V("origin"), V("i")), D(0))),
                "The center has all three coordinates zero."),
            Definition("distance", "d", "Shortest-walk distance", All("x", V("L"),
                Eq(Call("d", V("x")), App(Q("SimpleGraph", "dist"), V("contactGraph"),
                    V("origin"), V("x")))),
                "Distance is SimpleGraph.dist in the stated contact graph, the minimum walk length. "
                    + "The construction of paths below shows every vertex is reachable from the origin."),
            Definition("point-group", "W", "All signed coordinate permutations", GroupFormula(),
                "The group consists of all signed coordinate permutations, acting on integer triples "
                    + "by the displayed formula. The lattice is invariant: changing a sign preserves "
                    + "a coordinate modulo two, and permuting coordinates preserves their sum. "
                    + "The restricted action is literal evaluation of the same signed permutation. "
                    + "All reflections are included."),
            Definition("shell", "Shell", "A shell at any natural radius", All("n", Naturals(),
                Eq(Call("Shell", V("n")), SetOf("x", V("L"), Eq(Call("d", V("x")), V("n"))))),
                "The radius is any natural number, including zero."),
            Definition("orbits", "A", "The number of orbits on a shell", OrbitFormula(),
                "Restrict the orbit equivalence relation of the action on L to Shell n, and take "
                    + "the natural cardinality of its quotient. The distance formula shows the shells "
                    + "are invariant and finite. Sorting absolute coordinates is a theorem about this "
                    + "quotient and supplies no part of its definition."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("The formal generating-function identity"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let the absolute coordinates be sorted as c ≤ b ≤ a. Signed permutations "
                        + "preserve this sorted tuple, and any two integer triples with the same tuple "
                        + "are related by one signed permutation. Every orbit therefore has precisely "
                        + "one nonnegative sorted representative with even coordinate sum.")),
                    Paragraph(Text("Define a potential as the maximum of the largest absolute coordinate "
                        + "and half the sum of the three absolute coordinates, with natural floor division. "
                        + "Each contact step changes the largest absolute coordinate by at most one "
                        + "and the sum by at most two. The potential consequently gives a lower bound "
                        + "for walk length from zero.")),
                    Paragraph(Text("For a nonnegative sorted representative, decrease the two largest "
                        + "coordinates by one when the middle coordinate is positive. Otherwise the "
                        + "smallest and middle coordinates are zero. If the potential is positive, "
                        + "the largest coordinate is at least two and even; decrease it by one and "
                        + "increase the middle coordinate to one. These steps decrease the potential "
                        + "by exactly one. Transport them by signed permutations and use strong "
                        + "induction to obtain a walk whose length equals the potential. Thus the "
                        + "graph distance is max(a,(a+b+c)/2).")),
                    Paragraph(Text("If a ≥ b+c, put u=b−c and t=(a−b−c)/2. This gives a unique "
                        + "triple of natural numbers with (a,b,c)=(2c+u+2t,c+u,c) and distance "
                        + "2c+u+2t. If a<b+c, put p=(b+c−a)/2, q=(a+c−b)/2 and r=(a+b−c)/2. "
                        + "The even sum and triangle inequality give 1≤p≤q≤r. Write p=1+i, "
                        + "q=p+j and r=q+k. The distance is 3+3i+2j+k. The two cases are disjoint "
                        + "and exhaust all representatives.")),
                    Paragraph(Text("Counting fibers of a sum of two weights corresponds to multiplying "
                        + "their formal series: separate the fiber by the two weights, whose sum "
                        + "is the required coefficient index. A natural variable with weight w "
                        + "contributes the geometric series in X to the power w. The first region "
                        + "has weights 2,1,2; the second has weights 3,2,1 and an initial shift of "
                        + "three. Clearing the common denominator leaves (1−X³)+X³(1−X²)=1−X⁵. "
                        + "The coefficients and the identity are over the integers, with no convergence "
                        + "condition. At radius zero the first region contributes its zero triple."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula LatticeFormula() => Eq(V("L"), SetOf("x", Arrow(Call("Fin", D(3)), Integers()),
        Eq(Call("mod", Add(Add(Coord(V("x"), 0), Coord(V("x"), 1)), Coord(V("x"), 2)), D(2)), D(0))));

    private static Formula ContactFormula()
    {
        var x = V("x"); var y = V("y");
        Formula Delta(byte i) => Call("abs", Sub(Coord(y, i), Coord(x, i)));
        return All("x", V("L"), All("y", V("L"), Iff(
            App(Q("SimpleGraph", "Adj"), V("contactGraph"), x, y),
            Or(And(Eq(Delta(0), D(1)), And(Eq(Delta(1), D(1)), Eq(Coord(y, 2), Coord(x, 2)))),
               Or(And(Eq(Delta(0), D(1)), And(Eq(Coord(y, 1), Coord(x, 1)), Eq(Delta(2), D(1)))),
                  And(Eq(Coord(y, 0), Coord(x, 0)), And(Eq(Delta(1), D(1)), Eq(Delta(2), D(1)))))))));
    }

    private static Formula GroupFormula()
    {
        var i = V("i"); var x = V("x"); var s = V("s"); var p = V("p");
        var indices = Call("Fin", D(3));
        var signs = All("i", indices,
            Or(Eq(App(s, i), D(1)), Eq(App(s, i), Sub(D(0), D(1)))));
        var transform = All("x", Arrow(indices, Integers()), All("i", indices,
            Eq(App(App(V("w"), x), i), Mul(App(s, i), App(x, App(p, i))))));
        return All("w", Call("Perm", Arrow(indices, Integers())),
            Iff(Seq(V("w"), Sp, InMacro, Sp, V("W")),
                Ex("p", Call("Perm", indices), Ex("s", Arrow(indices, Integers()),
                    And(signs, transform)))));

    }

    private static Formula OrbitFormula()
    {
        var inclusion = Cast(Q("Subtype", "val"), Arrow(Call("Shell", V("n")), V("L")));
        var relation = App(Q("MulAction", "orbitRel"), V("W"), V("L"));
        var restricted = App(Q("Setoid", "comap"), inclusion, relation);
        return All("n", Naturals(), Eq(Call("A", V("n")),
            App(Q("Nat", "card"), Call("Quotient", restricted))));
    }

    private static Formula ResultFormula()
    {
        var x = Q("PowerSeries", "X");
        var series = App(Q("PowerSeries", "mk"),
            Seq(LambdaLower, Sp, V("n"), Sp, Mapsto, Sp, Cast(Call("A", V("n")), Integers())));
        return Eq(Mul(Mul(Mul(Paren(Sub(D(1), x)), Pow(Paren(Sub(D(1), Pow(x, D(2)))), D(2))),
            Paren(Sub(D(1), Pow(x, D(3))))), series), Sub(D(1), Pow(x, D(5))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Paren(a), Sp, To, Sp, b);
    private static Formula Coord(Formula x, byte i) => App(x, D(i));
    private static Formula Cast(Formula a, Formula t) => Paren(Seq(a, Colon, Sp, t));
    private static Formula SetOf(string name, Formula t, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, t, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Iff(Formula a, Formula b) => Seq(Paren(a), Sp, F.Iff, Sp, Paren(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula t, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, t, Comma, Sp, Paren(body));
    private static Formula Ex(string name, Formula t, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, t, Comma, Sp, Paren(body));
    private static Formula And(Formula a, Formula b) => Seq(Paren(a), Sp, Land, Sp, Paren(b));
    private static Formula Or(Formula a, Formula b) => Seq(Paren(a), Sp, Lor, Sp, Paren(b));
}
