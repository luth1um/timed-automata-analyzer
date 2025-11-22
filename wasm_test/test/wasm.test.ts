import { describe, it, expect } from "vitest";
import { findUnreachableLocations, Location, Switch, TimedAutomaton } from "../../pkg";

describe("The analyzer wasm", () => {
  it("should return an empty array when all locations are reachable", () => {
    // given
    const loc0 = new Location("loc0", true);
    const loc1 = new Location("loc1", false);
    const sw = new Switch(loc0, undefined, "action", [], loc1);
    const ta = new TimedAutomaton([loc0, loc1], [], [sw]);

    // when
    const unreachable = findUnreachableLocations(ta);

    // then
    expect(unreachable).toHaveLength(0);
  });

  it("should return the name of the unreachable location when there is an unreachable location", () => {
    // given
    const locInit = new Location("locInit", true);
    const unreachableName = "locUnreachable";
    const locUnreachable = new Location(unreachableName, false);
    const sw = new Switch(locInit, undefined, "action", [], locInit); // self-loop
    const ta = new TimedAutomaton([locInit, locUnreachable], [], [sw]);

    // when
    const unreachable = findUnreachableLocations(ta);

    // then
    expect(unreachable).toEqual([unreachableName]);
  });

  it("should throw when the input is an empty TA", () => {
    // given
    const ta = new TimedAutomaton([], [], []);
    const checkFn = () => findUnreachableLocations(ta);

    // when / then
    expect(checkFn).toThrowError("The input TA failed some validation checks.");
  });
});
