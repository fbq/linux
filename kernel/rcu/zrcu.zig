const kernel = @import("kernel");

pub export fn do_zig(a: i32) void {
    _ = kernel.print("Hello, zig, %d and %d\n", .{ a, @as(i32, 42) });
}
