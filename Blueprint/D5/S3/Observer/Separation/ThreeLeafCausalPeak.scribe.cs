using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class ThreeLeafCausalPeakDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Separation/ThreeLeafCausalPeak.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Modular three-leaf promises have uniformly bounded cut costs and unbounded causal-tree peak.",
        H("Bounded Cuts and Unbounded Three-Leaf Causal Peak"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-leaf-world"),
                DeclarationHandle.Create(Prefix + "World"),
                H("The modular promise"),
                StatementSource.FromAuthor(WorldFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural number m, World m is the subtype of triples (x,y,z) in "
                        + "ZMod m with z=x+y. Write D_m for this type. The equality is in the "
                        + "cyclic ring ZMod m. In the theorem m is twice the square of K, with K at least two, "
                        + "so m is positive, D_m is finite and nonempty, and it has m squared elements."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-point"),
                DeclarationHandle.Create(Prefix + "point"),
                H("Legal triples and coordinate observations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m and x,y in ZMod m, point x y is the legal triple (x,y,x+y). "
                        + "The functions xcoord, ycoord and zcoord send a legal triple to its "
                        + "first, second and third coordinate. Every pair (x,y) has this unique "
                        + "completion. The pair (x,z) completes as (x,z-x,z), and (y,z) completes "
                        + "as (z-y,y,z). Thus every two-coordinate projection is the full product."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-cut-admits"),
                DeclarationHandle.Create(Prefix + "CutAdmits"),
                H("One-way encoding of a raw-input cut"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary types Omega, L and R, a Boolean function f on Omega, "
                        + "observations l:Omega to L and r:Omega to R, and a natural number n, "
                        + "CutAdmits f l r n means that there exist an arbitrary type A, a total "
                        + "encoder e:L to A and a total decoder d:A to R to Bool such that both "
                        + "Nat.card(range(e composed with l)) is at most n and, for every w in "
                        + "Omega, d(e(l(w)),r(w))=f(w). There is no finiteness hypothesis on A. "
                        + "Only messages reached from Omega enter the cardinality. For positive m "
                        + "the promise D_m and these ranges are finite, even when A is infinite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-cut-cost"),
                DeclarationHandle.Create(Prefix + "cutCost"),
                H("Minimum reachable cut cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the same f,l,r, cutCost f l r is the natural-number infimum "
                            + "sInf of the set of n satisfying CutAdmits f l r n. For the cuts "
                            + "of D_m below, this set is nonempty, so the infimum is an attained "
                            + "natural minimum. Cardinality counts message values, not bits.")),
                    Paragraph(Text(
                        "Write c_X(m,f) for cutCost f xcoord (ycoord,zcoord), c_Y(m,f) for "
                            + "cutCost f ycoord (xcoord,zcoord), and c_Z(m,f) for cutCost f "
                            + "zcoord (xcoord,ycoord). Here a pair of coordinate maps sends w "
                            + "to the ordered pair of their values. Write c_XY(m,f) for cutCost "
                            + "f (xcoord,ycoord) zcoord, c_XZ(m,f) for cutCost f "
                            + "(xcoord,zcoord) ycoord, and c_YZ(m,f) for cutCost f "
                            + "(ycoord,zcoord) xcoord. Finally c_XYZ(m,f) is cutCost f id "
                            + "(the constant map to Unit). Its encoder sees the entire legal "
                            + "triple and its decoder receives no complementary input."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-protocol"),
                DeclarationHandle.Create(Prefix + "Protocol"),
                H("A protocol on the fixed tree ((X,Y),Z)"),
                StatementSource.FromAuthor(ProtocolFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each m, Protocol m consists of four arbitrary types A,B,C,M and "
                        + "the five displayed total maps. Each alphabet may be infinite; no "
                        + "Fintype or finite-alphabet assumption is imposed. The leaf maps "
                        + "alpha, beta and gamma each see only their own raw coordinate. "
                        + "The internal map tau receives only alpha(x) and beta(y), and the "
                        + "root map rho receives only that internal message and gamma(z). "
                        + "Correctness will be required only on legal triples."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-internal"),
                DeclarationHandle.Create(Prefix + "internal"),
                H("The actual internal message"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m, protocol p and w in World m, internal p w is "
                        + "p.tau(p.alpha(xcoord w),p.beta(ycoord w)). Its range is taken "
                        + "over legal worlds w. It counts jointly reachable outputs of the "
                        + "internal node. For this promise every pair (x,y) is legal after "
                        + "completion, so every pair of reachable alpha and beta messages "
                        + "is jointly reachable."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-correct"),
                DeclarationHandle.Create(Prefix + "Correct"),
                H("Correctness on the promise"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m, protocol p and f:World m to Bool, Correct p f means "
                        + "that for every w in World m, "
                        + "p.rho(internal p w,p.gamma(zcoord w))=f(w). The same legal "
                        + "world supplies all three coordinates in this equation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-peak"),
                DeclarationHandle.Create(Prefix + "peak"),
                H("The four reachable message cardinalities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m and p:Protocol m, peak p is "
                        + "max(max(Nat.card(range p.alpha),Nat.card(range p.beta)), "
                        + "max(Nat.card(range p.gamma),Nat.card(range(internal p)))). "
                        + "The three leaf ranges are over ZMod m; the internal range is over "
                        + "World m. For positive m all four are finite and nonempty. Ambient "
                        + "alphabet cardinalities and unreachable entries of the total maps "
                        + "do not enter this maximum. The final Boolean output is not an "
                        + "additional term in the peak."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-peak-optimum"),
                DeclarationHandle.Create(Prefix + "peakOpt"),
                H("The attained natural optimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m and f:World m to Bool, peakOpt f is sInf of the set of "
                        + "natural numbers n for which there exists p:Protocol m with "
                        + "Correct p f and peak p at most n. This quantifies over all four "
                        + "alphabet types and all five causal maps. When m is positive, "
                        + "a correct protocol exists: let alpha and beta send their raw "
                        + "coordinates, gamma send a constant, tau send the ordered pair, "
                        + "and rho evaluate f at its unique legal completion. Thus the "
                        + "admissible set is nonempty, its natural infimum belongs to it, "
                        + "and a correct protocol attains the optimal peak. Write P_T(m,f) "
                        + "for this number, with T fixed as ((X,Y),Z)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-tables"),
                DeclarationHandle.Create(Prefix + "Tables"),
                H("Finite labels for reachable messages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Tables m K is the product of three function types ZMod m to Fin K, "
                        + "one function type Fin K to Fin K to Fin K, and one function type "
                        + "Fin K to Fin K to Bool. For a tuple (a,b,c,t,r), evaluate sends "
                        + "w to r(t(a(xcoord w),b(ycoord w)),c(zcoord w)). When K is at least "
                        + "two and m is twice its square, these finite tables represent all "
                        + "protocols of peak at most K after relabeling their reachable images; "
                        + "they do not restrict the alphabet types "
                        + "in the definition of Protocol."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-leaf-causal-peak-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Bounded raw-input cuts and unbounded causal peak"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural K at least two, set m to twice the square of K. There exists "
                            + "one Boolean function f on this fixed modular promise for which "
                            + "all eight displayed clauses hold simultaneously. The singleton "
                            + "costs are exactly one, the XY cost is exactly two, the XZ and YZ "
                            + "costs are at most two, the full-input cost is exactly two, and "
                            + "the attained optimal causal peak is strictly greater than K.")),
                    Paragraph(Text(
                        "A protocol of peak at most K can relabel each of its four reachable "
                            + "images inside Fin K. Because every pair of raw X and Y inputs "
                            + "occurs in a legal world, the internal map on any pair of "
                            + "reachable child messages lands in its actual reachable image. "
                            + "Inverse labels and arbitrary values on unused labels extend "
                            + "these maps to a total finite table with the same Boolean output "
                            + "at every legal world.")),
                    Paragraph(Text(
                        "There are K to the power (3m+K squared), multiplied by 2 to the "
                            + "power K squared, such finite tables, while there are 2 to the "
                            + "power m squared Boolean functions on D_m. For K at least two, "
                            + "K is at most 2 to the power K and 7K+1 is strictly less than "
                            + "four times the square of K. With m twice the square of K, "
                            + "these inequalities make the table "
                            + "count strictly smaller than the number of Boolean functions. "
                            + "Choose a function outside the image of evaluation. Every "
                            + "correct protocol for it then has peak greater than K, and "
                            + "attainment transfers the strict bound to peakOpt.")),
                    Paragraph(Text(
                        "Each complementary coordinate pair uniquely reconstructs the "
                            + "legal world, so singleton encoders can be constant. Every "
                            + "two-coordinate encoder can reconstruct that world and send "
                            + "f directly as a Boolean. A function depending only on z has "
                            + "a protocol of peak at most two, so the chosen f cannot have "
                            + "that form. A one-message XY encoding would make f depend only "
                            + "on z; hence the XY cost is exactly two. The same function is "
                            + "nonconstant, which makes its full-input cost exactly two.")),
                    Paragraph(Text(
                        "All six nonempty proper raw-input cuts therefore have cost at most "
                            + "two. These encoders have access to joint raw coordinates on "
                            + "their own side of the cut. On the causal tree the internal "
                            + "node has access only to the two leaf messages produced by "
                            + "the same protocol. Small separate cut costs thus coexist with "
                            + "an unbounded family of optimal causal peaks."))),
                DescribeRole.Theorem))));

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));

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

    private static Formula WorldFormula()
    {
        Formula m = F.Id("m");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula domain = new Formula.Subscript(F.Id("D"), m);
        Formula group = Apply(Name("ZMod"), m);
        return Disp(Seq(
            Forall, Sp, m, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            domain, Sp, Eq, Sp, OpenBrace, Sp,
            Open, x, Comma, Sp, y, Comma, Sp, z, Close, Sp, InMacro, Sp,
            group, Caret, Grp(D(3)), Sp, Mid, Sp,
            z, Sp, Eq, Sp, x, Sp, Plus, Sp, y, Sp, CloseBrace));
    }

    private static Formula ProtocolFormula()
    {
        Formula group = Apply(Name("ZMod"), F.Id("m"));
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula c = F.Id("C");
        Formula message = F.Id("M");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            a, Comma, Sp, b, Comma, Sp, c, Comma, Sp, message,
            Colon, Sp, Name("Type"), Comma, RowBreak,
            Alpha, Colon, Sp, group, Sp, To, Sp, a, Comma, Sp,
            Beta, Colon, Sp, group, Sp, To, Sp, b, Comma, Sp,
            GammaLower, Colon, Sp, group, Sp, To, Sp, c, Comma, RowBreak,
            Tau, Colon, Sp, a, Sp, To, Sp, b, Sp, To, Sp, message, Comma, Sp,
            Rho, Colon, Sp, message, Sp, To, Sp, c, Sp, To, Sp, Name("Bool"),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ResultFormula()
    {
        Formula k = F.Id("K");
        Formula m = F.Id("m");
        Formula f = F.Id("f");
        Formula domain = new Formula.Subscript(F.Id("D"), m);
        Formula costX = Apply(new Formula.Subscript(F.Id("c"), F.Id("X")), m, f);
        Formula costY = Apply(new Formula.Subscript(F.Id("c"), F.Id("Y")), m, f);
        Formula costZ = Apply(new Formula.Subscript(F.Id("c"), F.Id("Z")), m, f);
        Formula costXY = Apply(new Formula.Subscript(F.Id("c"), F.Id("XY")), m, f);
        Formula costXZ = Apply(new Formula.Subscript(F.Id("c"), F.Id("XZ")), m, f);
        Formula costYZ = Apply(new Formula.Subscript(F.Id("c"), F.Id("YZ")), m, f);
        Formula costXYZ = Apply(new Formula.Subscript(F.Id("c"), F.Id("XYZ")), m, f);
        Formula optimum = Apply(new Formula.Subscript(F.Id("P"), F.Id("T")), m, f);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(2), Sp, Leq, Sp, k, Sp, Rightarrow, RowBreak,
            Name("let"), Sp, m, Sp, Eq, Sp, D(2), Sp, k, Caret, Grp(D(2)), Semi, Sp,
            Exists, Sp, f, Colon, Sp, domain, Sp, To, Sp, Name("Bool"), Comma, RowBreak,
            costX, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            costY, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            costZ, Sp, Eq, Sp, D(1), Sp, Land, RowBreak,
            costXY, Sp, Eq, Sp, D(2), Sp, Land, Sp,
            costXZ, Sp, Leq, Sp, D(2), Sp, Land, Sp,
            costYZ, Sp, Leq, Sp, D(2), Sp, Land, RowBreak,
            costXYZ, Sp, Eq, Sp, D(2), Sp, Land, Sp,
            k, Sp, Lt, Sp, optimum,
            End, Grp(F.Id("gathered"))));
    }
}
