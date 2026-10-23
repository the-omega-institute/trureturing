using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SixWindowForcingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local separation and six-window forcing.",
        H("Local separation and six-window forcing"),
        Blocks(Describe.Lean(
            DescribeId.Create("sixwindowforcing-algebra"),
            DeclarationHandle.Create("D5/S1/Digit/Infinite/SixWindowForcing.algebra"),
            H("Golden parameter relations"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The three-bit contraction satisfies g^2+4g=1 and 4/17<g<17/72. The reciprocal golden ratio satisfies t=(1+g)/2 and t^2=(1-g)/2."))),
            DescribeRole.Theorem), Describe.Lean(
            DescribeId.Create("sixwindowforcing-result"),
            DeclarationHandle.Create("D5/S1/Digit/Infinite/SixWindowForcing.result"),
            H("Shared colors force alternating source blocks"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Two legal infinite Boolean sources are observed through the same finite "
                + "sequence of closed expanded cells. One step deletes three bits. "
                + "The signed contraction is -g, where g is the cube of the reciprocal "
                + "golden ratio. The four interior separation types have ordered labels "
                + "(3,0), (0,5), (5,2), and (2,25).")),
                Paragraph(Text(
                "For 0 <= nu < lambda, write delta = lambda - nu. The critical closed "
                + "expansions have lower endpoints (-1, -6t^2/5, g-2t^2/5, "
                + "t-3t^2/5, 2t-4t^2/5, 2t) and upper endpoints (-t^2, g-t^2/5, "
                + "t-2t^2/5, 2t-3t^2/5, 2t+t^2/5, 1+t). At radius nu each "
                + "interior endpoint moves inward by delta. The two outer endpoints "
                + "remain -1 and 1+t. End colors force labels 3 and 25 respectively, "
                + "so unequal labels at a common current color give one of the four "
                + "interior ordered pairs, or its reversal.")),
                Paragraph(Text(
                "At a common current interior color i with its ordered low and high "
                + "labels, the next coordinates u and v satisfy u <= s_i-delta/g "
                + "and s_i+delta/g <= v, where s_i=-1+i(1+t)/5. These bounds need "
                + "only the current color and ordered labels. If the next color is "
                + "also common, it is respectively 0, 1, 1, or 2; a common next label "
                + "must respectively be 3, 0, 0, or 5.")),
                Paragraph(Text(
                "With three common colors, a common next label in type three requires "
                + "delta <= max(K31,K32), and in type four requires delta <= K4. "
                + "Here K31=(47g-11)/50, K32=(5-21g)/20, and "
                + "K4=(9g-2)/25=2g^3/(5(1+g^2)). For type two, four common "
                + "colors and a common next label require delta <= J, where "
                + "J=2g^4/(5(1+g^3)).")),
                Paragraph(Text(
                "When delta exceeds the corresponding necessary bound, type two "
                + "with four common colors, and types three and four with three "
                + "common colors, force the next ordered pair of type one, one, and "
                + "two respectively. If delta > g^4/5, a type-one pair with three "
                + "common colors forces colors (1,0,2) and windows (3,3,5) and "
                + "(0,3,0). If delta > J and delta > g^4/5, iterating the type-two "
                + "return forces the six-window words (3,3,5,0,3,0) and "
                + "(0,3,0,3,3,5) from any starting position whose ordered labels "
                + "are (3,0), for every positive "
                + "number m of repetitions using exactly 6m common colors. The "
                + "propagation uses no colors beyond position 6m-1 relative to "
                + "the starting position.")),
                Paragraph(Text(
                "For nu <= rho=(239g-44)/380, all four strict budget inequalities "
                + "hold. Thus the conclusions also apply throughout the original "
                + "range at or below the finite-delay critical radius."))),
            DescribeRole.Theorem))));
}
