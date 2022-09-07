const linux = @cImport({
    @cDefine("__KERNEL__", {});
    @cInclude("linux/compiler_types.h");
    @cInclude("linux/printk.h");
});

pub fn print(comptime fmt: []const u8, arg: anytype) void {
    _ = @call(.{}, linux._printk, .{@ptrCast([*c]const u8, fmt)} ++ arg);
}
